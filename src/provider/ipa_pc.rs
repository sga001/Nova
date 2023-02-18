//! This module implements `EvaluationEngine` using an IPA-based polynomial commitment scheme
#![allow(clippy::too_many_arguments)]
use crate::{
  errors::NovaError,
  provider::pedersen::CommitmentGensExtTrait,
  spartan::polynomial::EqPolynomial,
  traits::{
    commitment::{CommitmentEngineTrait, CommitmentGensTrait, CommitmentTrait},
    evaluation::EvaluationEngineTrait,
    AppendToTranscriptTrait, ChallengeTrait, Group,
  },
  Commitment, CommitmentGens, CompressedCommitment, CE,
};
use core::{cmp::max, iter};
use ff::Field;
use merlin::Transcript;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;
use rand::rngs::OsRng;

/// Provides an implementation of generators for proving evaluations
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct EvaluationGens<G: Group> {
  gens_v: CommitmentGens<G>, // This is a generator for vectors
  gens_s: CommitmentGens<G>, // This is a generator for scalars
}

/// Provides an implementation of a polynomial evaluation argument
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct EvaluationArgument<G: Group> {
  nifs: Vec<NIFSForInnerProduct<G>>,
  ipa: InnerProductArgument<G>,
}

/// Provides an implementation of a polynomial evaluation engine using IPA
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EvaluationEngine<G: Group> {
  _p: PhantomData<G>,
}

impl<G> EvaluationEngineTrait<G> for EvaluationEngine<G>
where
  G: Group,
  CommitmentGens<G>: CommitmentGensExtTrait<G, CE = G::CE>,
{
  type CE = G::CE;
  type EvaluationGens = EvaluationGens<G>;
  type EvaluationArgument = EvaluationArgument<G>;

  fn setup(gens: &<Self::CE as CommitmentEngineTrait<G>>::CommitmentGens) -> Self::EvaluationGens {
    EvaluationGens {
      gens_v: gens.clone(),
      gens_s: CommitmentGens::<G>::new(b"ipa", 1),
    }
  }

  fn prove_batch(
    gens: &Self::EvaluationGens,
    transcript: &mut Transcript,
    comms: &[Commitment<G>],
    polys: &[Vec<G::Scalar>],
    points: &[Vec<G::Scalar>],
    evals: &[G::Scalar], 
  ) -> Result<Self::EvaluationArgument, NovaError> {
    // sanity checks (these should never fail)
    assert!(polys.len() >= 2);
    assert_eq!(comms.len(), polys.len());
    assert_eq!(comms.len(), points.len());
    assert_eq!(comms.len(), evals.len());

    // Need to commit to evals (which are basically "c"). 
    // Then pass evals and blinding factors to InnerProductWitness 
    // and pass commitments to InnerProductInstance

    // Commit to eval[0]
    let r_eval_0 = G::Scalar::random(&mut OsRng); 
    let comm_eval_0 = CE::<G>::commit(&gens.gen_s, &evals[0], &r_eval_0);

    let mut U_folded = InnerProductInstance::new(
      &comms[0],
      &EqPolynomial::new(points[0].clone()).evals(),
      &comm_eval_0,
    );

    // Record value of eval and randomness used in commitment in the witness
    
    let r_polys_0 = G::Scalar::random(&mut OsRng); 
    let mut W_folded = InnerProductWitness::new(&polys[0], &r_polys_0, &evals[0], &r_eval_0);
    let mut nifs = Vec::new();

    for i in 1..polys.len() {
      // Commit to eval[i]
      let r_eval_i = G::Scalar::random(&mut OsRng); 
      let r_polys_i = G::Scalar::random(&mut OsRng); 

      let comm_eval_i = CE::<G>::commit(&gens.gen_s, &evals[i], &r_eval_i);

      // perform the folding
      let (n, u, w) = NIFSForInnerProduct::prove(
        &gens,
        &U_folded,
        &W_folded,
        &InnerProductInstance::new(
          &comms[i],
          &EqPolynomial::new(points[i].clone()).evals(),
          &comm_eval_i,
        ),
        &InnerProductWitness::new(&polys[i], &r_polys_i, &evals[i], &r_eval_i),
        transcript,
      );
      nifs.push(n);
      U_folded = u;
      W_folded = w;
    }

    let ipa = InnerProductArgument::prove(&gens.gens_v, &gens.gens_s, &U_folded, &W_folded, transcript)?;

    Ok(EvaluationArgument { nifs, ipa })
  }

  /// A method to verify purported evaluations of a batch of polynomials
  fn verify_batch(
    gens: &Self::EvaluationGens,
    transcript: &mut Transcript,
    comms: &[Commitment<G>],
    points: &[Vec<G::Scalar>],
    comm_evals: &[Commitment<G>],
    arg: &Self::EvaluationArgument,
  ) -> Result<(), NovaError> {
    // sanity checks (these should never fail)
    assert!(comms.len() >= 2);
    assert_eq!(comms.len(), points.len());
    assert_eq!(comms.len(), comm_evals.len());

    let mut U_folded = InnerProductInstance::new(
      &comms[0],
      &EqPolynomial::new(points[0].clone()).evals(),
      &comm_evals[0],
    );
    let mut num_vars = points[0].len();
    for i in 1..comms.len() {
      let u = arg.nifs[i - 1].verify(
        &U_folded,
        &InnerProductInstance::new(
          &comms[i],
          &EqPolynomial::new(points[i].clone()).evals(),
          &comm_evals[i],
        ),
        transcript,
      );
      U_folded = u;
      num_vars = max(num_vars, points[i].len());
    }

    arg.ipa.verify(
      &gens.gens_v,
      &gens.gens_s,
      (2_usize).pow(num_vars as u32),
      &U_folded,
      transcript,
    )?;

    Ok(())
  }
}

fn inner_product<T>(a: &[T], b: &[T]) -> T
where
  T: Field + Send + Sync,
{
  assert_eq!(a.len(), b.len());
  (0..a.len())
    .into_par_iter()
    .map(|i| a[i] * b[i])
    .reduce(T::zero, |x, y| x + y)
}

/// An inner product instance consists of a commitment to a vector `a` and another vector `b`
/// and the claim that y = <x, a>.
pub struct InnerProductInstance<G: Group> {
  comm_x_vec: Commitment<G>,
  a_vec: Vec<G::Scalar>,
  comm_y: Commitment<G>, // commitment to scalar c
}

impl<G: Group> InnerProductInstance<G> {
  fn new(comm_x_vec: &Commitment<G>, a_vec: &[G::Scalar], comm_y: &Commitment<G>) -> Self {
    InnerProductInstance {
      comm_x_vec: *comm_x_vec,
      a_vec: a_vec.to_vec(),
      comm_y: *comm_y,
    }
  }

  fn pad(&self, n: usize) -> InnerProductInstance<G> {
    let mut a_vec = self.a_vec.clone();
    a_vec.resize(n, G::Scalar::zero());
    InnerProductInstance {
      comm_x_vec: self.comm_x_vec,
      a_vec,
      comm_y: self.comm_y,
    }
  }
}

struct InnerProductWitness<G: Group> {
  x_vec: Vec<G::Scalar>,
  r_x: Vec<G::Scalar>,
  y: G::Scalar,
  r_y: G::Scalar,
}

impl<G: Group> InnerProductWitness<G> {
  fn new(x_vec: &[G::Scalar], r_x: &G::Scalar, y: &G::Scalar, r_y: &G::Scalar) -> Self {
    InnerProductWitness {
      x_vec: x_vec.to_vec(),
      r_x: *r_x,
      y: *y,
      r_y: *r_y,
    }
  }

  fn pad(&self, n: usize) -> InnerProductWitness<G> {
    let mut x_vec = self.x_vec.clone();
    x_vec.resize(n, G::Scalar::zero());
    InnerProductWitness { 
      x_vec,
      r_x: self.r_x,
      y: self.y,
      r_y: self.r_y
    }
  }
}

/// A non-interactive folding scheme (NIFS) for inner product relations
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NIFSForInnerProduct<G: Group> {
  comm_cross_term: Commitment<G>, // commitment to cross term (which is a scalar)
}

impl<G: Group> NIFSForInnerProduct<G> {
  fn protocol_name() -> &'static [u8] {
    b"NIFSForInnerProduct"
  }

  fn prove(
    gens: &EvaluationGens<G>,
    U1: &InnerProductInstance<G>,
    W1: &InnerProductWitness<G>,
    U2: &InnerProductInstance<G>,
    W2: &InnerProductWitness<G>,
    transcript: &mut Transcript,
  ) -> (Self, InnerProductInstance<G>, InnerProductWitness<G>) {
    transcript.append_message(b"protocol-name", Self::protocol_name());

    // pad the instances and witness so they are of the same length
    let U1 = U1.pad(max(U1.a_vec.len(), U2.a_vec.len()));
    let U2 = U2.pad(max(U1.a_vec.len(), U2.a_vec.len()));
    let W1 = W1.pad(max(U1.a_vec.len(), U2.a_vec.len()));
    let W2 = W2.pad(max(U1.a_vec.len(), U2.a_vec.len()));

    // add the two commitments and two public vectors to the transcript
    U1.comm_x_vec
      .append_to_transcript(b"U1_comm_x_vec", transcript);
    U1.a_vec.append_to_transcript(b"U1_a_vec", transcript);
    U2.comm_x_vec
      .append_to_transcript(b"U2_comm_x_vec", transcript);
    U2.a_vec.append_to_transcript(b"U2_a_vec", transcript);

    // compute the cross-term
    let cross_term = inner_product(&W1.x_vec, &U2.a_vec) + inner_product(&W2.x_vec, &U1.a_vec);

    // commit to the cross-term
    let r_cross = G::Scalar::random(&mut OsRng); 
    let comm_cross = CE::<G>::commit(&gens.gen_s, &cross_term, &r_cross);
 
    // add the commitment of the cross-term to the transcript
    comm_cross.append_to_transcript(b"cross_term", transcript);

    // obtain a random challenge
    let r = G::Scalar::challenge(b"r", transcript);

    // fold the vectors and their inner product
    let x_vec = W1
      .x_vec
      .par_iter()
      .zip(W2.x_vec.par_iter())
      .map(|(x1, x2)| *x1 + r * x2)
      .collect::<Vec<G::Scalar>>();
    let a_vec = U1
      .a_vec
      .par_iter()
      .zip(U2.a_vec.par_iter())
      .map(|(x1, x2)| *x1 + r * x2)
      .collect::<Vec<G::Scalar>>();

    // fold using the cross term and fold x_vec as well
    let y = W1.y + r * r * W2.y + r * cross_term;
    let comm_x_vec = U1.comm_x_vec + U2.comm_x_vec * r;
    let r_x = W1.r_x +  W2.r_x * r; 

    // generate commitment to y
    let r_y = G::Scalar::random(&mut OsRng);
    let comm_y = CE::<G>::commit(&gens.gen_s, &y, &r_y);

    let W = InnerProductWitness { 
      x_vec,
      r_x,
      y,
      r_y,
    };

    let U = InnerProductInstance {
      comm_x_vec,
      a_vec,
      comm_y,
    };

    (NIFSForInnerProduct { comm_cross_term: comm_cross }, U, W)
  }

  fn verify(
    &self,
    U1: &InnerProductInstance<G>,
    U2: &InnerProductInstance<G>,
    transcript: &mut Transcript,
  ) -> InnerProductInstance<G> {
    transcript.append_message(b"protocol-name", Self::protocol_name());

    // pad the instances so they are of the same length
    let U1 = U1.pad(max(U1.a_vec.len(), U2.a_vec.len()));
    let U2 = U2.pad(max(U1.a_vec.len(), U2.a_vec.len()));

    // add the two commitments and two public vectors to the transcript
    U1.comm_x_vec
      .append_to_transcript(b"U1_comm_x_vec", transcript);
    U1.a_vec.append_to_transcript(b"U1_a_vec", transcript);
    U2.comm_x_vec
      .append_to_transcript(b"U2_comm_x_vec", transcript);
    U2.a_vec.append_to_transcript(b"U2_a_vec", transcript);

    // add the commitment to the cross-term to the transcript
    self
      .comm_cross_term
      .append_to_transcript(b"cross_term", transcript);

    // obtain a random challenge
    let r = G::Scalar::challenge(b"r", transcript);

    // fold the vectors and their inner product
    let a_vec = U1
      .a_vec
      .par_iter()
      .zip(U2.a_vec.par_iter())
      .map(|(x1, x2)| *x1 + r * x2)
      .collect::<Vec<G::Scalar>>();

    let comm_y = U1.comm_y + r * r * U2.comm_y + r * self.comm_cross_term;
    let comm_x_vec = U1.comm_x_vec + U2.comm_x_vec * r;

    InnerProductInstance {
      comm_x_vec,
      a_vec,
      comm_y,
    }
  }
}

/// An inner product argument
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
struct InnerProductArgument<G: Group> {
  P_L_vec: Vec<CompressedCommitment<G>>,
  P_R_vec: Vec<CompressedCommitment<G>>,
  z_1: G::Scalar,
  z_2: G::Scalar,
  _p: PhantomData<G>,
}

impl<G> InnerProductArgument<G>
where
  G: Group,
  CommitmentGens<G>: CommitmentGensExtTrait<G, CE = G::CE>,
{
  fn protocol_name() -> &'static [u8] {
    b"inner product argument"
  }


  fn bullet_reduce(P: CompressedCommitment<G>, 
                   r_P: &G::Scalar,
                   x_vec: &[G::Scalar],
                   a_vec: &[G::Scalar],
                   y: &G::Scalar,
                   gens: &CommitmentGens<G>,
                   gens_y: &CommitmentGens<G>,
                   transcript: &mut Transcript) 
    -> Result<
      (
        CompressedCommitment<G>, // P'
        G::Scalar,               // r_P'
        CompressedCommitment<G>, // P_L
        CompressedCommitment<G>, // P_R
        G::Scalar,               // y_prime
        Vec<G::Scalar>,          // x_vec'
        Vec<G::Scalar>,          // a_vec'
        CommitmentGens<G>,       // gens'
      ),
      NovaError,
    > {
      let n = x_vec.len();
      let (gens_L, gens_R) = gens.split_at(n / 2);

      let y_L = inner_product(&x_vec[0..n / 2], &a_vec[n / 2..n]);
      let y_R = inner_product(&x_vec[n / 2..n], &a_vec[0..n / 2]);

      let r_L = G::Scalar::random(&mut OsRng); 
      let r_R = G::Scalar::random(&mut OsRng); 

      let P_L = CE::<G>::commit(
        &gens_R.combine(&gens_y),
        &x_vec[0..n / 2]
          .iter()
          .chain(iter::once(&y_L))
          .copied()
          .collect::<Vec<G::Scalar>>(),
        &r_L,
      )
      .compress();

      let P_R = CE::<G>::commit(
        &gens_L.combine(&gens_y),
        &x_vec[n / 2..n]
          .iter()
          .chain(iter::once(&y_R))
          .copied()
          .collect::<Vec<G::Scalar>>(),
        &r_R,
      )
      .compress();

      P_L.append_to_transcript(b"L", transcript);
      P_R.append_to_transcript(b"R", transcript);

      let chal = G::Scalar::challenge(b"challenge_r", transcript);
      let chal_square = chal * chal;
      let chal_inverse = chal.invert().unwrap();
      let chal_inverse_square = chal_inverse * chal_inverse;

      // fold the left half and the right half
      let x_vec_prime = x_vec[0..n / 2]
        .par_iter()
        .zip(x_vec[n / 2..n].par_iter())
        .map(|(x_L, x_R)| *x_L * chal + chal_inverse * *x_R)
        .collect::<Vec<G::Scalar>>();

      let a_vec_prime = a_vec[0..n / 2]
        .par_iter()
        .zip(a_vec[n / 2..n].par_iter())
        .map(|(a_L, a_R)| *a_L * chal_inverse + chal * *a_R)
        .collect::<Vec<G::Scalar>>();

      let gens_folded = gens.fold(&chal_inverse, &chal);

      let y_prime = chal_square * y_L + y + chal_inverse_square * y_R;
      let P_prime = P_L * chal_square + P + P_R * chal_inverse_square;
      let r_P_prime = r_L * chal_square + r_P + r_R * chal_inverse_square;

      Ok((P_prime, r_P_prime, P_L, P_R, y_prime, x_vec_prime, a_vec_prime, gens_folded))
    }

  fn prove(
    gens: &CommitmentGens<G>,
    gens_y: &CommitmentGens<G>, 
    U: &InnerProductInstance<G>,
    W: &InnerProductWitness<G>,
    transcript: &mut Transcript,
  ) -> Result<Self, NovaError> {
    transcript.append_message(b"protocol-name", Self::protocol_name());

    // The goal here is to prove that x_vec * a_vec = y. 
    // We have a hiding vector commitment to x_vec, and a hiding commitment to y. 
    // a_vec is a vector in the clear.

    // We will prove this based on Hyrax's Figure 7 and 8.
    // Translation of variables from this code to Hyrax's paper
    //
    // Code                     Hyrax
    // ------------------------------
    // x_vec                    \vec{x}
    // r_x                      r_\Xi  
    // comm_x_vec               \Xi
    //
    // a_vec                    \vec{a} 
    // 
    // y                        y
    // comm_y                   \tau
    // r_y                      r_\tau

    // P                        \Upsilon
    // r_P                      r_\Upsilon
    //
    // gens                     vec<g_i>
    // gens_y                   g


    if U.a_vec.len() != W.x_vec.len() {
      return Err(NovaError::InvalidInputLength);
    }

    U.comm_x_vec.append_to_transcript(b"comm_x_vec", transcript);
    U.a_vec.append_to_transcript(b"a_vec", transcript);
    U.comm_y.append_to_transcript(b"y", transcript);
    
    // sample a random challenge for commiting to the inner product 
    let chal = G::Scalar::challenge(b"r", transcript);
    let gens_y = gens_y.scale(&chal);

    // Scaling to be compatible with Bulletproofs figure 1
    let mut P = U.comm_x_vec + U.comm_y * chal;

    // two vectors to hold the logarithmic number of group elements, and their masks
    let mut P_L_vec: Vec<CompressedCommitment<G>> = Vec::new();
    let mut P_R_vec: Vec<CompressedCommitment<G>> = Vec::new();

    let mut r_P = W.r_x + W.r_y;

    // we create mutable copies of vectors and generators
    let mut x_vec = W.x_vec.to_vec();
    let mut a_vec = U.a_vec.to_vec();
    let mut gens = gens.clone();
    let mut y = W.y.clone();

    for _i in 0..(U.a_vec.len() as f64).log2() as usize {
      let (P_prime, r_P_prime, P_L, P_R, y_prime, x_vec_prime, a_vec_prime, gens_prime) =
        Self::bullet_reduce(&P, &r_P, &x_vec, &a_vec, &y, &gens, &gens_y, transcript)?;

      P_L_vec.push(P_L);
      P_R_vec.push(P_R);

      P = P_prime;
      r_P = r_P_prime;
      y = y_prime;
      x_vec = x_vec_prime;
      a_vec = a_vec_prime;
      gens = gens_prime;
    }

    // This is after the recursive calls to bullet_reduce in Hyrax
    let P_hat = P;
    let r_P_hat = r_P;
    let y_hat = y;
    let a_hat = a_vec;
    let g_hat = gens;

    let d = G::Scalar::random(&mut OsRng); 
    let r_delta = G::Scalar::random(&mut OsRng); 
    let r_beta = G::Scalar::random(&mut OsRng); 

    let delta = CE::<G>::commit(
        &g_hat,
        &[d.clone()], 
        &r_delta,
      )
      .compress();

    let beta = CE::<G>::commit(
      &gens_y,
      &[d],
      &r_beta,
    ).compress();

    let chal = G::Scalar::challenge(b"chal_bullet", transcript);
    
    let z_1 = d + chal * y_hat;
    let z_2 = a_hat * (chal * r_P_hat + r_beta) + r_delta;


    Ok(InnerProductArgument {
      P_L_vec,
      P_R_vec,
      z_1,
      z_2,
      _p: Default::default(),
    })
  }

  fn verify(
    &self,
    gens: &CommitmentGens<G>,
    gens_y: &CommitmentGens<G>,
    n: usize,
    U: &InnerProductInstance<G>,
    transcript: &mut Transcript,
  ) -> Result<(), NovaError> {
    transcript.append_message(b"protocol-name", Self::protocol_name());
    if U.a_vec.len() != n
      || n != (1 << self.L_vec.len())
      || self.L_vec.len() != self.R_vec.len()
      || self.L_vec.len() >= 32
    {
      return Err(NovaError::InvalidInputLength);
    }

    U.comm_x_vec.append_to_transcript(b"comm_x_vec", transcript);
    U.a_vec.append_to_transcript(b"a_vec", transcript);
    U.comm_y.append_to_transcript(b"y", transcript);

    // sample a random challenge for scaling commitment
    let chal = G::Scalar::challenge(b"r", transcript);
    let gens_y = gens_y.scale(&chal);

    let P = U.comm_x_vec + U.comm_y * chal;

    let batch_invert = |v: &[G::Scalar]| -> Result<Vec<G::Scalar>, NovaError> {
      let mut products = vec![G::Scalar::zero(); v.len()];
      let mut acc = G::Scalar::one();

      for i in 0..v.len() {
        products[i] = acc;
        acc *= v[i];
      }

      // we can compute an inversion only if acc is non-zero
      if acc == G::Scalar::zero() {
        return Err(NovaError::InvalidInputLength);
      }

      // compute the inverse once for all entries
      acc = acc.invert().unwrap();

      let mut inv = vec![G::Scalar::zero(); v.len()];
      for i in 0..v.len() {
        let tmp = acc * v[v.len() - 1 - i];
        inv[v.len() - 1 - i] = products[v.len() - 1 - i] * acc;
        acc = tmp;
      }

      Ok(inv)
    };

    // compute a vector of public coins using self.L_vec and self.R_vec
    let chal = (0..self.L_vec.len())
      .map(|i| {
        self.L_vec[i].append_to_transcript(b"L", transcript);
        self.R_vec[i].append_to_transcript(b"R", transcript);
        G::Scalar::challenge(b"challenge_r", transcript)
      })
      .collect::<Vec<G::Scalar>>();

    // precompute scalars necessary for verification
    let chal_square: Vec<G::Scalar> = (0..self.L_vec.len())
      .into_par_iter()
      .map(|i| chal[i] * chal[i])
      .collect();
    let chal_inverse = batch_invert(&chal)?;
    let chal_inverse_square: Vec<G::Scalar> = (0..self.L_vec.len())
      .into_par_iter()
      .map(|i| chal_inverse[i] * chal_inverse[i])
      .collect();

    // compute the vector with the tensor structure
    let s = {
      let mut s = vec![G::Scalar::zero(); n];
      s[0] = {
        let mut v = G::Scalar::one();
        for chal_inverse_i in &chal_inverse {
          v *= chal_inverse_i;
        }
        v
      };
      for i in 1..n {
        let pos_in_chal = (31 - (i as u32).leading_zeros()) as usize;
        s[i] = s[i - (1 << pos_in_chal)] * chal_square[(self.L_vec.len() - 1) - pos_in_chal];
      }
      s
    };

    let gens_hat = {
      let y = CE::<G>::commit(gens, &s).compress();
      CommitmentGens::<G>::reinterpret_commitments_as_gens(&[y])?
    };

    let a_hat = inner_product(&U.a_vec, &s);

    let P_hat = {
      let gens_folded = {
        let gens_L = CommitmentGens::<G>::reinterpret_commitments_as_gens(&self.L_vec)?;
        let gens_R = CommitmentGens::<G>::reinterpret_commitments_as_gens(&self.R_vec)?;
        let gens_P = CommitmentGens::<G>::reinterpret_commitments_as_gens(&[P.compress()])?;
        gens_L.combine(&gens_R).combine(&gens_P)
      };

      CE::<G>::commit(
        &gens_folded,
        &chal_square
          .iter()
          .chain(chal_inverse_square.iter())
          .chain(iter::once(&G::Scalar::one()))
          .copied()
          .collect::<Vec<G::Scalar>>(),
      )
    };

    if P_hat
      == CE::<G>::commit(
        &gens_hat.combine(&gens_y),
        &[self.x_hat, self.x_hat * a_hat],
      )
    {
      Ok(())
    } else {
      Err(NovaError::InvalidIPA)
    }
  }
}
