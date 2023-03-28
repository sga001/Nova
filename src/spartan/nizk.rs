#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
use crate::errors::NovaError;
use crate::traits::{
  commitment::{CommitmentEngineTrait, CommitmentGensTrait, CommitmentTrait, CompressedCommitmentTrait},  
  AppendToTranscriptTrait, ChallengeTrait, Group, evaluation::EvaluationEngineTrait};
use crate::{Commitment, CommitmentGens, CompressedCommitment, CE};
use ff::Field;
use merlin::Transcript;
use serde::{Deserialize, Serialize};
use rand::rngs::OsRng;


#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct DotProductProof<G: Group> {
  delta: CompressedCommitment<G>,
  beta: CompressedCommitment<G>,
  z: Vec<G::Scalar>,
  z_delta: G::Scalar,
  z_beta: G::Scalar,
}


impl<G: Group> DotProductProof<G> {

  fn protocol_name() -> &'static [u8] {
    b"dot product proof"
  }

  pub fn compute_dotproduct(a: &[G::Scalar], b: &[G::Scalar]) -> G::Scalar {
    assert_eq!(a.len(), b.len());
    (0..a.len()).map(|i| a[i] * b[i]).sum()
  }

  pub fn prove(
    gens_1: &CommitmentGens<G>, // generator of size 1
    gens_n: &CommitmentGens<G>, // generators of size n
    transcript: &mut Transcript,
    x_vec: &[G::Scalar],
    blind_x: &G::Scalar,
    a_vec: &[G::Scalar],
    y: &G::Scalar,
    blind_y: &G::Scalar,
  ) -> (Self, CompressedCommitment<G>, CompressedCommitment<G>) {
    transcript.append_message(b"protocol-name", DotProductProof::protocol_name());

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());
    assert_eq!(gens_n.gens.len(), a_vec.len());
    assert_eq!(gens_1.gens.len(), 1);

    // produce randomness for the proofs
    let d_vec = (0..n)
        .map(|_i| G::Scalar::random(&mut OsRng))
        .collect::<Vec<G::Scalar>>();


    let r_delta = G::Scalar::random(&mut OsRng);
    let r_beta = G::Scalar::random(&mut OsRng);

    let Cx = CE::<G>::commit(gens_n, x_vec, blind_x).compress();
    Cx.append_to_transcript(b"Cx", transcript);

    let Cy = CE::<G>::commit(gens_1, &[y.clone()], blind_y).compress();
    Cy.append_to_transcript(b"Cy", transcript);

    a_vec.append_to_transcript(b"a", transcript);

    let delta = CE::<G>::commit(gens_n, &d_vec, &r_delta).compress();
    delta.append_to_transcript(b"delta", transcript);

    let dotproduct_a_d = DotProductProof::compute_dotproduct(a_vec, &d_vec);

    let beta = CE::<G>::commit(gens_1, &[dotproduct_a_d], &r_beta).compress();
    beta.append_to_transcript(b"beta", transcript);

    let c = G::Scalar::challenge(b"c", transcript);

    let z = (0..d_vec.len())
      .map(|i| c * x_vec[i] + d_vec[i])
      .collect::<Vec<G::Scalar>>();

    let z_delta = c * blind_x + r_delta;
    let z_beta = c * blind_y + r_beta;

    (
      DotProductProof {
        delta,
        beta,
        z,
        z_delta,
        z_beta,
      },
      Cx,
      Cy,
    )
  }


  pub fn verify(
    &self,
    gens_1: &CommitmentGens<G>, // generator of size 1
    gens_n: &CommitmentGens<G>, // generator of size n
    transcript: &mut Transcript,
    a_vec: &[G::Scalar],
    Cx: &CompressedCommitment<G>,
    Cy: &CompressedCommitment<G>,
  )-> Result<(), NovaError> {
    assert_eq!(gens_n.gens.len(), a_vec.len());  
    assert_eq!(gens_1.gens.len(), 1);

    transcript.append_message(b"protocol-name", DotProductProof::protocol_name());

    Cx.append_to_transcript(b"Cx", transcript);
    Cy.append_to_transcript(b"Cy", transcript);
    a_vec.append_to_transcript(b"a", transcript);
    self.delta.append_to_transcript(b"delta", transcript);
    self.beta.append_to_transcript(b"beta", transcript);

    let c = G::Scalar::challenge(b"c", transcript);

    let mut result = 
      Cx.decompress()? * c  + self.delta.decompress()? == 
      CE::<G>::commit(gens_n, &self.z, &self.z_delta);

    let dotproduct_z_a = DotProductProof::compute_dotproduct(&self.z, a_vec);
    result &= Cy.decompress()? * c + self.beta.decompress()?
      == CE::<G>::commit(gens_1, &[dotproduct_z_a], &self.z_beta);

    if result {
      Ok(())
    } else {
      Err(NovaError::InvalidDotProductProof)
    }
  }
}
