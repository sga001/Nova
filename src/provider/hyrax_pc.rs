//! This module implements the Hyrax polynomial commitment scheme
#![allow(clippy::too_many_arguments)]
use crate::{
  errors::NovaError,
  provider::ipa_pc::{InnerProductArgument, InnerProductInstance, InnerProductWitness},
  provider::pedersen::CommitmentGensExtTrait,
  spartan::polynomial::{EqPolynomial, MultilinearPolynomial},
  traits::{
    commitment::{
      CommitmentEngineTrait, CommitmentGensTrait, CommitmentTrait, CompressedCommitmentTrait,
    },
    evaluation::GetGeneratorsTrait,
    AppendToTranscriptTrait, Group,
  },
  Commitment, CommitmentGens, CompressedCommitment,
};
use ff::Field;
use merlin::Transcript;
use rand::rngs::OsRng;
use rayon::prelude::*;

/// Structure that holds the blinds of a PC
pub struct PolyCommitBlinds<G: Group> {
  /// Blinds
  pub blinds: Vec<G::Scalar>,
}

/// Structure that holds Poly Commits
#[derive(Debug)]
pub struct PolyCommit<G: Group> {
  /// Commitment
  pub comm: Vec<CompressedCommitment<G>>,
}

impl<G: Group> AppendToTranscriptTrait for PolyCommit<G> {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, b"poly_commitment_begin");
    for c in &self.comm {
      c.append_to_transcript(b"poly_commitment_share", transcript);
    }
    transcript.append_message(label, b"poly_commitment_end");
  }
}

/// Hyrax PC generators and functions to commit and prove evaluation
pub struct HyraxPC<G: Group> {
  gens_v: CommitmentGens<G>, // generator for vectors
  gens_s: CommitmentGens<G>, // generator for scalars (eval)
}

impl<G: Group> GetGeneratorsTrait<G> for HyraxPC<G> {
  fn get_scalar_gen(&self) -> &CommitmentGens<G> {
    &self.gens_s
  }

  fn get_vector_gen(&self) -> &CommitmentGens<G> {
    &self.gens_v
  }
}

impl<G: Group> HyraxPC<G>
where
  G: Group,
  CommitmentGens<G>: CommitmentGensExtTrait<G, CE = G::CE>,
{
  /// Derives generators for Hyrax PC, where num_vars is the number of variables in multilinear poly
  pub fn new(num_vars: usize, label: &'static [u8]) -> Self {
    let (_left, right) = EqPolynomial::<G::Scalar>::compute_factored_lens(num_vars);
    let gens_v = CommitmentGens::<G>::new(label, right);
    let gens_s =
      CommitmentGens::<G>::new_with_blinding_gen(b"gens_s", 1, &gens_v.get_blinding_gen());
    HyraxPC { gens_v, gens_s }
  }

  fn commit_inner(
    &self,
    poly: &MultilinearPolynomial<G::Scalar>,
    blinds: &[G::Scalar],
  ) -> PolyCommit<G> {
    let L_size = blinds.len();
    let R_size = poly.len() / L_size;

    assert_eq!(L_size * R_size, poly.len());

    let comm = (0..L_size)
      .into_par_iter()
      .map(|i| {
        G::CE::commit(
          &self.gens_v,
          &poly.get_Z()[R_size * i..R_size * (i + 1)],
          &blinds[i],
        )
        .compress()
      })
      .collect();

    PolyCommit { comm }
  }

  /// Commits to a multilinear polynomial and returns commitment and blind
  pub fn commit(
    &self,
    poly: &MultilinearPolynomial<G::Scalar>,
  ) -> (PolyCommit<G>, PolyCommitBlinds<G>) {
    let n = poly.len();
    let ell = poly.get_num_vars();
    assert_eq!(n, (2usize).pow(ell as u32));

    let (left_num_vars, right_num_vars) = EqPolynomial::<G::Scalar>::compute_factored_lens(ell);
    let L_size = (2usize).pow(left_num_vars as u32);
    let R_size = (2usize).pow(right_num_vars as u32);
    assert_eq!(L_size * R_size, n);

    let blinds = PolyCommitBlinds {
      blinds: (0..L_size).map(|_| G::Scalar::random(&mut OsRng)).collect(),
    };

    (self.commit_inner(poly, &blinds.blinds), blinds)
  }

  /// Proves the evaluation of polynomial at a random point r
  pub fn prove_eval(
    &self,
    poly: &MultilinearPolynomial<G::Scalar>,
    poly_com: &PolyCommit<G>,
    blinds: &PolyCommitBlinds<G>,
    r: &[G::Scalar],      // point at which the polynomial is evaluated
    Zr: &G::Scalar,       // evaluation of poly(r)
    blind_Zr: &G::Scalar, // blind for Zr
    transcript: &mut Transcript,
  ) -> Result<
    (
      InnerProductInstance<G>,
      InnerProductWitness<G>,
      InnerProductArgument<G>,
    ),
    NovaError,
  > {
    transcript.append_message(b"protocol-name", b"polynomial evaluation proof");
    poly_com.append_to_transcript(b"poly_com", transcript);

    // assert vectors are of the right size
    assert_eq!(poly.get_num_vars(), r.len());

    let (left_num_vars, right_num_vars) = EqPolynomial::<G::Scalar>::compute_factored_lens(r.len());
    let L_size = (2usize).pow(left_num_vars as u32);
    let R_size = (2usize).pow(right_num_vars as u32);

    assert_eq!(blinds.blinds.len(), L_size);

    // compute the L and R vectors (these depend only on the public challenge r so they are public)
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();
    assert_eq!(L.len(), L_size);
    assert_eq!(R.len(), R_size);

    // compute the vector underneath L*Z and the L*blinds
    // compute vector-matrix product between L and Z viewed as a matrix
    let LZ = poly.bound(&L);
    let LZ_blind: G::Scalar = (0..L.len())
      .map(|i| blinds.blinds[i] * L[i])
      .fold(G::Scalar::one(), |acc, item| acc * item);

    // Translation between this stuff and IPA
    // LZ = x_vec
    // LZ_blind = r_x
    // Zr = y
    // blind_Zr = r_y
    // R = a_vec

    // Commit to LZ and Zr
    let com_LZ = G::CE::commit(&self.gens_v, &LZ, &LZ_blind);
    let com_Zr = G::CE::commit(&self.gens_s, &[Zr.clone()], blind_Zr);

    // a dot product argument (IPA) of size R_size
    let ipa_instance = InnerProductInstance::<G>::new(&com_LZ, &R, &com_Zr);
    let ipa_witness = InnerProductWitness::<G>::new(&LZ, &LZ_blind, Zr, blind_Zr);
    let ipa = InnerProductArgument::<G>::prove(
      &self.gens_v,
      &self.gens_s,
      &ipa_instance,
      &ipa_witness,
      transcript,
    )?;

    Ok((ipa_instance, ipa_witness, ipa))
  }

  /// Verifies the proof showing the evaluation of a committed polynomial at a random point
  pub fn verify_eval(
    &self,
    r: &[G::Scalar], // point at which the polynomial was evaluated
    poly_com: &PolyCommit<G>,
    com_Zr: &Commitment<G>, // commitment to evaluation
    ipa: &InnerProductArgument<G>,
    transcript: &mut Transcript,
  ) -> Result<(), NovaError> {
    transcript.append_message(b"protocol-name", b"polynomial evaluation proof");
    poly_com.append_to_transcript(b"poly_com", transcript);

    // compute L and R
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();

    // compute a weighted sum of commitments and L
    let C_decompressed: Vec<Commitment<G>> = poly_com
      .comm
      .iter()
      .map(|pt| pt.decompress().unwrap())
      .collect();
    let gens = CommitmentGens::<G>::from_commitments(&C_decompressed);
    let com_LZ = G::CE::commit(&gens, &L, &G::Scalar::zero()); // computes MSM of commitment and L

    let ipa_instance = InnerProductInstance::<G>::new(&com_LZ, &R, &com_Zr);

    ipa.verify(
      &self.gens_v,
      &self.gens_s,
      L.len(),
      &ipa_instance,
      transcript,
    )
  }
}
