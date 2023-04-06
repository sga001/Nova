//! This module implements RelaxedR1CSSNARKTrait using Spartan that is generic
//! over the polynomial commitment and evaluation argument (i.e., a PCS)
mod nizk;
pub mod polynomial;
mod sumcheck;

use crate::{
  errors::NovaError,
  r1cs::{R1CSGens, R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness},
  traits::{
    commitment::{
      CommitmentEngineTrait, CommitmentGensTrait, CommitmentTrait, CompressedCommitmentTrait,
    },
    evaluation::{EvaluationEngineTrait, GetEvalCommitmentsTrait, GetGeneratorsTrait},
    snark::{ProverKeyTrait, RelaxedR1CSSNARKTrait, VerifierKeyTrait},
    AppendToTranscriptTrait, ChallengeTrait, Group,
  },
  CommitmentGens, CompressedCommitment,
};
use ff::Field;
use itertools::concat;
use merlin::Transcript;
use nizk::{EqualityProof, KnowledgeProof, ProductProof};
use polynomial::{EqPolynomial, MultilinearPolynomial, SparsePolynomial};
use rand::rngs::OsRng;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use sumcheck::ZKSumcheckProof;

///A type that represents generators for commitments used in sumcheck
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SumcheckGens<G: Group> {
  /// 1 Generator
  pub gens_1: CommitmentGens<G>,
  /// 3 Generators
  pub gens_3: CommitmentGens<G>,
  /// 4 Generators
  pub gens_4: CommitmentGens<G>,
}

impl<G: Group> SumcheckGens<G> {
  /// Creates new generators for sumcheck
  pub fn new(label: &'static [u8], scalar_gen: &CommitmentGens<G>) -> Self {
    let gens_1 = scalar_gen.clone();
    let gens_3 =
      CommitmentGens::<G>::new_exact_with_blinding_gen(label, 3, &gens_1.get_blinding_gen());
    let gens_4 =
      CommitmentGens::<G>::new_exact_with_blinding_gen(label, 4, &gens_1.get_blinding_gen());

    Self {
      gens_1,
      gens_3,
      gens_4,
    }
  }
}

/// A type that represents the prover's key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProverKey<G: Group, EE: EvaluationEngineTrait<G, CE = G::CE>> {
  gens: EE::EvaluationGens,
  sumcheck_gens: SumcheckGens<G>,
  S: R1CSShape<G>,
}

impl<G: Group, EE: EvaluationEngineTrait<G, CE = G::CE>> ProverKeyTrait<G> for ProverKey<G, EE> {
  fn new(gens: &R1CSGens<G>, S: &R1CSShape<G>) -> Self {
    let gens = EE::setup(&gens.gens);
    let scalar_gen = &gens.get_scalar_gen();

    ProverKey {
      gens,
      sumcheck_gens: SumcheckGens::<G>::new(b"gens_s", scalar_gen),
      S: S.clone(),
    }
  }
}

/// A type that represents the verifier's key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct VerifierKey<G: Group, EE: EvaluationEngineTrait<G, CE = G::CE>> {
  gens: EE::EvaluationGens,
  sumcheck_gens: SumcheckGens<G>,
  S: R1CSShape<G>,
}

impl<G: Group, EE: EvaluationEngineTrait<G, CE = G::CE>> VerifierKeyTrait<G>
  for VerifierKey<G, EE>
{
  fn new(gens: &R1CSGens<G>, S: &R1CSShape<G>) -> Self {
    let gens = EE::setup(&gens.gens);
    let scalar_gen = &gens.get_scalar_gen();

    VerifierKey {
      gens,
      sumcheck_gens: SumcheckGens::<G>::new(b"gens_s", scalar_gen),
      S: S.clone(),
    }
  }
}

/// A succinct proof of knowledge of a witness to a relaxed R1CS instance
/// The proof is produced using Spartan's combination of the sum-check and
/// the commitment to a vector viewed as a polynomial commitment
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RelaxedR1CSSNARK<G: Group, EE: EvaluationEngineTrait<G, CE = G::CE>> {
  sc_proof_outer: ZKSumcheckProof<G>,
  claims_outer: (
    CompressedCommitment<G>,
    CompressedCommitment<G>,
    CompressedCommitment<G>,
    CompressedCommitment<G>,
  ),
  sc_proof_inner: ZKSumcheckProof<G>,
  pok_claims_inner: (KnowledgeProof<G>, ProductProof<G>),
  proof_eq_sc_outer: EqualityProof<G>,
  proof_eq_sc_inner: EqualityProof<G>,
  eval_arg: EE::EvaluationArgument,
}

impl<G: Group, EE: EvaluationEngineTrait<G, CE = G::CE>> RelaxedR1CSSNARKTrait<G>
  for RelaxedR1CSSNARK<G, EE>
{
  type ProverKey = ProverKey<G, EE>;
  type VerifierKey = VerifierKey<G, EE>;

  /// produces a succinct proof of satisfiability of a RelaxedR1CS instance
  fn prove(
    pk: &Self::ProverKey,
    U: &RelaxedR1CSInstance<G>,
    W: &RelaxedR1CSWitness<G>,
  ) -> Result<Self, NovaError> {
    let mut transcript = Transcript::new(b"RelaxedR1CSSNARK");

    // sanity check that R1CSShape has certain size characteristics
    assert_eq!(pk.S.num_cons.next_power_of_two(), pk.S.num_cons);
    assert_eq!(pk.S.num_vars.next_power_of_two(), pk.S.num_vars);
    assert_eq!(pk.S.num_io.next_power_of_two(), pk.S.num_io);
    assert!(pk.S.num_io < pk.S.num_vars);

    // append the R1CSShape and RelaxedR1CSInstance to the transcript
    pk.S.append_to_transcript(b"S", &mut transcript);
    U.append_to_transcript(b"U", &mut transcript);

    // compute the full satisfying assignment by concatenating W.W, U.u, and U.X
    let mut z = concat(vec![W.W.clone(), vec![U.u], U.X.clone()]);

    let (num_rounds_x, num_rounds_y) = (
      (pk.S.num_cons as f64).log2() as usize,
      ((pk.S.num_vars as f64).log2() as usize + 1),
    );

    // outer sum-check
    let tau = (0..num_rounds_x)
      .map(|_i| G::Scalar::challenge(b"challenge_tau", &mut transcript))
      .collect();

    let mut poly_tau = MultilinearPolynomial::new(EqPolynomial::new(tau).evals());

    let (mut poly_Az, mut poly_Bz, poly_Cz, mut poly_uCz_E) = {
      let (poly_Az, poly_Bz, poly_Cz) = pk.S.multiply_vec(&z)?;
      let poly_uCz_E = (0..pk.S.num_cons)
        .map(|i| U.u * poly_Cz[i] + W.E[i])
        .collect::<Vec<G::Scalar>>();
      (
        MultilinearPolynomial::new(poly_Az),
        MultilinearPolynomial::new(poly_Bz),
        MultilinearPolynomial::new(poly_Cz),
        MultilinearPolynomial::new(poly_uCz_E),
      )
    };

    let comb_func_outer =
      |poly_A_comp: &G::Scalar,
       poly_B_comp: &G::Scalar,
       poly_C_comp: &G::Scalar,
       poly_D_comp: &G::Scalar|
       -> G::Scalar { *poly_A_comp * (*poly_B_comp * *poly_C_comp - *poly_D_comp) };

    let (sc_proof_outer, r_x, _claims_outer, blind_claim_post_outer) =
      ZKSumcheckProof::prove_cubic_with_additive_term(
        &G::Scalar::zero(), // claim is zero
        &G::Scalar::zero(), // blind for claim is also zero
        num_rounds_x,
        &mut poly_tau,
        &mut poly_Az,
        &mut poly_Bz,
        &mut poly_uCz_E,
        comb_func_outer,
        &pk.sumcheck_gens.gens_1,
        &pk.sumcheck_gens.gens_4,
        &mut transcript,
      )?;

    assert_eq!(poly_tau.len(), 1);
    assert_eq!(poly_Az.len(), 1);
    assert_eq!(poly_Bz.len(), 1);
    assert_eq!(poly_uCz_E.len(), 1);

    let (tau_claim, Az_claim, Bz_claim) = (&poly_tau[0], &poly_Az[0], &poly_Bz[0]);

    let Cz_claim = poly_Cz.evaluate(&r_x);

    let (Az_blind, Bz_blind, Cz_blind, prod_Az_Bz_blind) = (
      G::Scalar::random(&mut OsRng),
      G::Scalar::random(&mut OsRng),
      G::Scalar::random(&mut OsRng),
      G::Scalar::random(&mut OsRng),
    );

    let (pok_Cz_claim, comm_Cz_claim) = {
      KnowledgeProof::<G>::prove(
        &pk.sumcheck_gens.gens_1,
        &mut transcript,
        &Cz_claim,
        &Cz_blind,
      )
    }?;

    let (proof_prod, comm_Az_claim, comm_Bz_claim, comm_prod_Az_Bz_claims) = {
      let prod = *Az_claim * *Bz_claim;
      ProductProof::<G>::prove(
        &pk.sumcheck_gens.gens_1,
        &mut transcript,
        Az_claim,
        &Az_blind,
        Bz_claim,
        &Bz_blind,
        &prod,
        &prod_Az_Bz_blind,
      )
    }?;

    // prove the final step of sumcheck outer
    let taus_bound_rx = tau_claim;

    // Evaluate E at r_x. We do this to compute blind and claim of outer sumcheck
    let eval_E = MultilinearPolynomial::new(W.E.clone()).evaluate(&r_x);
    let blind_eval_E = G::Scalar::random(&mut OsRng);

    let blind_expected_claim_outer =
      *taus_bound_rx * (prod_Az_Bz_blind - (U.u * Cz_blind + blind_eval_E));
    let claim_post_outer = *taus_bound_rx * (*Az_claim * *Bz_claim - (U.u * Cz_claim + eval_E));

    let (proof_eq_sc_outer, _C1, _C2) = EqualityProof::<G>::prove(
      &pk.sumcheck_gens.gens_1,
      &mut transcript,
      &claim_post_outer,
      &blind_expected_claim_outer,
      &claim_post_outer,
      &blind_claim_post_outer,
    )?;

    // Combine the three claims into a single claim
    let r_A = G::Scalar::challenge(b"challenge_rA", &mut transcript);
    let r_B = G::Scalar::challenge(b"challenge_rB", &mut transcript);
    let r_C = G::Scalar::challenge(b"challenge_rC", &mut transcript);

    let claim_inner_joint = r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim;
    let blind_claim_inner_joint = r_A * Az_blind + r_B * Bz_blind + r_C * Cz_blind;

    let poly_ABC = {
      // compute the initial evaluation table for R(\tau, x)
      let evals_rx = EqPolynomial::new(r_x.clone()).evals();

      // Bounds "row" variables of (A, B, C) matrices viewed as 2d multilinear polynomials
      let compute_eval_table_sparse =
        |S: &R1CSShape<G>, rx: &[G::Scalar]| -> (Vec<G::Scalar>, Vec<G::Scalar>, Vec<G::Scalar>) {
          assert_eq!(rx.len(), S.num_cons);

          let inner = |M: &Vec<(usize, usize, G::Scalar)>, M_evals: &mut Vec<G::Scalar>| {
            for (row, col, val) in M {
              M_evals[*col] += rx[*row] * val;
            }
          };

          let (A_evals, (B_evals, C_evals)) = rayon::join(
            || {
              let mut A_evals: Vec<G::Scalar> = vec![G::Scalar::zero(); 2 * S.num_vars];
              inner(&S.A, &mut A_evals);
              A_evals
            },
            || {
              rayon::join(
                || {
                  let mut B_evals: Vec<G::Scalar> = vec![G::Scalar::zero(); 2 * S.num_vars];
                  inner(&S.B, &mut B_evals);
                  B_evals
                },
                || {
                  let mut C_evals: Vec<G::Scalar> = vec![G::Scalar::zero(); 2 * S.num_vars];
                  inner(&S.C, &mut C_evals);
                  C_evals
                },
              )
            },
          );

          (A_evals, B_evals, C_evals)
        };

      let (evals_A, evals_B, evals_C) = compute_eval_table_sparse(&pk.S, &evals_rx);

      assert_eq!(evals_A.len(), evals_B.len());
      assert_eq!(evals_A.len(), evals_C.len());
      (0..evals_A.len())
        .into_par_iter()
        .map(|i| r_A * evals_A[i] + r_B * evals_B[i] + r_C * evals_C[i])
        .collect::<Vec<G::Scalar>>()
    };

    let poly_z = {
      z.resize(pk.S.num_vars * 2, G::Scalar::zero());
      z
    };

    let comb_func = |poly_A_comp: &G::Scalar, poly_B_comp: &G::Scalar| -> G::Scalar {
      *poly_A_comp * *poly_B_comp
    };

    let (sc_proof_inner, r_y, claims_inner, blind_claim_postsc_inner) =
      ZKSumcheckProof::prove_quad(
        &claim_inner_joint,
        &blind_claim_inner_joint,
        num_rounds_y,
        &mut MultilinearPolynomial::new(poly_z),
        &mut MultilinearPolynomial::new(poly_ABC),
        comb_func,
        &pk.sumcheck_gens.gens_1,
        &pk.sumcheck_gens.gens_3,
        &mut transcript,
      )?;

    let eval_W = MultilinearPolynomial::new(W.W.clone()).evaluate(&r_y[1..]);
    let blind_eval_W = G::Scalar::random(&mut OsRng);

    // prove the final step of inner sumcheck
    let blind_eval_Z_at_ry = (G::Scalar::one() - r_y[0]) * blind_eval_W;
    let blind_expected_claim_post_inner = claims_inner[1] * blind_eval_Z_at_ry;
    let claim_post_inner = claims_inner[0] * claims_inner[1];

    //TODO: sort this out

    let (proof_eq_sc_inner, _C1, _C2) = EqualityProof::prove(
      &pk.gens.get_scalar_gen(),
      &mut transcript,
      &claim_post_inner,
      &blind_expected_claim_post_inner,
      &claim_post_inner,
      &blind_claim_postsc_inner,
    )?;

    let eval_arg = EE::prove_batch(
      &pk.gens,
      &mut transcript,
      &[U.comm_E, U.comm_W],           // commitment to x_vec in Hyrax
      &[W.E.clone(), W.W.clone()],     // x_vec in Hyrax
      &[W.r_E.clone(), W.r_W.clone()], // decommitment to x_vec
      &[r_x, r_y[1..].to_vec()],
      &[eval_E, eval_W], // y_vec in Hyrax
      &[blind_eval_E, blind_eval_W],
    )?;

    Ok(RelaxedR1CSSNARK {
      sc_proof_outer,
      claims_outer: (
        comm_Az_claim,
        comm_Bz_claim,
        comm_Cz_claim,
        comm_prod_Az_Bz_claims,
      ),
      sc_proof_inner,
      pok_claims_inner: (pok_Cz_claim, proof_prod),
      proof_eq_sc_outer,
      proof_eq_sc_inner,
      eval_arg,
    })
  }

  /// verifies a proof of satisfiability of a RelaxedR1CS instance
  fn verify(&self, vk: &Self::VerifierKey, U: &RelaxedR1CSInstance<G>) -> Result<(), NovaError> {
    let mut transcript = Transcript::new(b"RelaxedR1CSSNARK");

    // append the R1CSShape and RelaxedR1CSInstance to the transcript
    vk.S.append_to_transcript(b"S", &mut transcript);
    U.append_to_transcript(b"U", &mut transcript);

    let (num_rounds_x, num_rounds_y) = (
      (vk.S.num_cons as f64).log2() as usize,
      ((vk.S.num_vars as f64).log2() as usize + 1),
    );

    // commitments for evaluations
    let comm_eval_E = self.eval_arg.get_eval_commitment(0);
    let comm_eval_W = self.eval_arg.get_eval_commitment(1);

    // derive the verifier's challenge tau
    let tau = (0..num_rounds_x)
      .map(|_i| G::Scalar::challenge(b"challenge_tau", &mut transcript))
      .collect::<Vec<G::Scalar>>();

    // outer sum-check
    let claim_outer_comm = G::CE::commit(
      &vk.sumcheck_gens.gens_1,
      &[G::Scalar::zero()],
      &G::Scalar::zero(),
    )
    .compress();

    let (comm_claim_post_outer, r_x) = self.sc_proof_outer.verify(
      &claim_outer_comm,
      num_rounds_x,
      3,
      &vk.sumcheck_gens.gens_1,
      &vk.sumcheck_gens.gens_4,
      &mut transcript,
    )?;

    // perform the intermediate sum-check test with claimed Az, Bz, and Cz
    let (comm_Az_claim, comm_Bz_claim, comm_Cz_claim, comm_prod_Az_Bz_claims) = &self.claims_outer;
    let (pok_Cz_claim, proof_prod) = &self.pok_claims_inner;

    pok_Cz_claim.verify(&vk.sumcheck_gens.gens_1, &mut transcript, comm_Cz_claim)?;

    proof_prod.verify(
      &vk.sumcheck_gens.gens_1,
      &mut transcript,
      comm_Az_claim,
      comm_Bz_claim,
      comm_prod_Az_Bz_claims,
    )?;

    let taus_bound_rx = EqPolynomial::new(tau).evaluate(&r_x);
    let comm_expected_claim_post_outer = ((comm_prod_Az_Bz_claims.decompress()?
      - (comm_Cz_claim.decompress()? * U.u + comm_eval_E.decompress()?))
      * taus_bound_rx)
      .compress();

    // verify proof that expected_claim_post_outer == claim_post_outer
    self.proof_eq_sc_outer.verify(
      &vk.sumcheck_gens.gens_1,
      &mut transcript,
      &comm_expected_claim_post_outer,
      &comm_claim_post_outer,
    )?;

    // inner sum-check

    // derive three public challenges and then derive a joint claim
    let r_A = G::Scalar::challenge(b"challenge_rA", &mut transcript);
    let r_B = G::Scalar::challenge(b"challenge_rB", &mut transcript);
    let r_C = G::Scalar::challenge(b"challenge_rC", &mut transcript);

    // r_A * comm_Az_claim + r_B * comm_Bz_claim + r_C * comm_Cz_claim;
    let comm_claim_inner = (comm_Az_claim.decompress()? * r_A
      + comm_Bz_claim.decompress()? * r_B
      + comm_Cz_claim.decompress()? * r_C)
      .compress();

    // verify the joint claim with a sum-check protocol
    let (comm_claim_post_inner, r_y) = self.sc_proof_inner.verify(
      &comm_claim_inner,
      num_rounds_y,
      2,
      &vk.sumcheck_gens.gens_1,
      &vk.sumcheck_gens.gens_3,
      &mut transcript,
    )?;

    // verify claim_inner_final
    let comm_eval_Z = {
      let eval_X = {
        // constant term
        let mut poly_X = vec![(0, U.u)];
        //remaining inputs
        poly_X.extend(
          (0..U.X.len())
            .map(|i| (i + 1, U.X[i]))
            .collect::<Vec<(usize, G::Scalar)>>(),
        );
        SparsePolynomial::new((vk.S.num_vars as f64).log2() as usize, poly_X).evaluate(&r_y[1..])
      };

      comm_eval_W.decompress()? * (G::Scalar::one() - r_y[0])
        + G::CE::commit(&vk.gens.get_scalar_gen(), &[eval_X], &G::Scalar::zero()) * r_y[0]
    };

    // perform the final check in the second sum-check protocol

    let evaluate_as_sparse_polynomial = |S: &R1CSShape<G>,
                                         r_x: &[G::Scalar],
                                         r_y: &[G::Scalar]|
     -> (G::Scalar, G::Scalar, G::Scalar) {
      let evaluate_with_table =
        |M: &[(usize, usize, G::Scalar)], T_x: &[G::Scalar], T_y: &[G::Scalar]| -> G::Scalar {
          (0..M.len())
            .map(|i| {
              let (row, col, val) = M[i];
              T_x[row] * T_y[col] * val
            })
            .fold(G::Scalar::zero(), |acc, x| acc + x)
        };

      let T_x = EqPolynomial::new(r_x.to_vec()).evals();
      let T_y = EqPolynomial::new(r_y.to_vec()).evals();
      let eval_A_r = evaluate_with_table(&S.A, &T_x, &T_y);
      let eval_B_r = evaluate_with_table(&S.B, &T_x, &T_y);
      let eval_C_r = evaluate_with_table(&S.C, &T_x, &T_y);
      (eval_A_r, eval_B_r, eval_C_r)
    };

    let (eval_A_r, eval_B_r, eval_C_r) = evaluate_as_sparse_polynomial(&vk.S, &r_x, &r_y);

    let claim_inner_final_expected =
      (comm_eval_Z * (r_A * eval_A_r + r_B * eval_B_r + r_C * eval_C_r)).compress();

    // verify proof that claim_inner_final_expected == claim_post_inner
    self.proof_eq_sc_inner.verify(
      &vk.sumcheck_gens.gens_1,
      &mut transcript,
      &claim_inner_final_expected,
      &comm_claim_post_inner,
    )?;

    // verify eval_W and eval_E
    EE::verify_batch(
      &vk.gens,
      &mut transcript,
      &[U.comm_E, U.comm_W],
      &[r_x, r_y[1..].to_vec()],
      &self.eval_arg,
    )?;

    Ok(())
  }
}
