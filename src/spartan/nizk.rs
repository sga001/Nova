#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
use crate::errors::NovaError;
use crate::traits::{
  commitment::{
    CommitmentEngineTrait, CommitmentGensTrait, CommitmentTrait, CompressedCommitmentTrait,
  },
  AppendToTranscriptTrait, ChallengeTrait, Group,
};
use crate::{CommitmentGens, CompressedCommitment, CE};
use ff::Field;
use merlin::Transcript;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct KnowledgeProof<G: Group> {
  alpha: CompressedCommitment<G>,
  z1: G::Scalar,
  z2: G::Scalar,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct EqualityProof<G: Group> {
  alpha: CompressedCommitment<G>,
  z: G::Scalar,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProductProof<G: Group> {
  alpha: CompressedCommitment<G>,
  beta: CompressedCommitment<G>,
  delta: CompressedCommitment<G>,
  z: [G::Scalar; 5],
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct DotProductProof<G: Group> {
  delta: CompressedCommitment<G>,
  beta: CompressedCommitment<G>,
  z: Vec<G::Scalar>,
  z_delta: G::Scalar,
  z_beta: G::Scalar,
}

impl<G: Group> KnowledgeProof<G> {
  fn protocol_name() -> &'static [u8] {
    b"knowledge proof"
  }

  pub fn prove(
    gens_n: &CommitmentGens<G>,
    transcript: &mut Transcript,
    x: &G::Scalar,
    r: &G::Scalar,
  ) -> Result<(KnowledgeProof<G>, CompressedCommitment<G>), NovaError> {
    transcript.append_message(b"protocol-name", KnowledgeProof::<G>::protocol_name());

    // produce two random scalars
    let t1 = G::Scalar::random(&mut OsRng);
    let t2 = G::Scalar::random(&mut OsRng);

    let C = G::CE::commit(gens_n, &[*x], r).compress();
    C.append_to_transcript(b"C", transcript);

    let alpha = G::CE::commit(gens_n, &[t1], &t2).compress();
    alpha.append_to_transcript(b"alpha", transcript);

    let c = G::Scalar::challenge(b"c", transcript);

    let z1 = *x * c + t1;
    let z2 = *r * c + t2;

    Ok((Self { alpha, z1, z2 }, C))
  }

  pub fn verify(
    &self,
    gens_n: &CommitmentGens<G>,
    transcript: &mut Transcript,
    C: &CompressedCommitment<G>,
  ) -> Result<(), NovaError> {
    transcript.append_message(b"protocol-name", KnowledgeProof::<G>::protocol_name());
    C.append_to_transcript(b"C", transcript);
    self.alpha.append_to_transcript(b"alpha", transcript);

    let c = G::Scalar::challenge(b"c", transcript);

    let lhs = G::CE::commit(gens_n, &[self.z1], &self.z2).compress();
    let rhs = (C.decompress()? * c + self.alpha.decompress()?).compress();

    if lhs == rhs {
      Ok(())
    } else {
      Err(NovaError::InvalidKnowledgeProof)
    }
  }
}

impl<G: Group> EqualityProof<G> {
  fn protocol_name() -> &'static [u8] {
    b"equality proof"
  }

  pub fn prove(
    gens_n: &CommitmentGens<G>,
    transcript: &mut Transcript,
    v1: &G::Scalar,
    s1: &G::Scalar,
    v2: &G::Scalar,
    s2: &G::Scalar,
  ) -> Result<
    (
      EqualityProof<G>,
      CompressedCommitment<G>,
      CompressedCommitment<G>,
    ),
    NovaError,
  > {
    transcript.append_message(b"protocol-name", EqualityProof::<G>::protocol_name());

    // produce a random scalar
    let r = G::Scalar::random(&mut OsRng);

    let C1 = G::CE::commit(gens_n, &[*v1], s1).compress();
    C1.append_to_transcript(b"C1", transcript);

    let C2 = G::CE::commit(gens_n, &[*v2], s2).compress();
    C2.append_to_transcript(b"C2", transcript);

    let alpha = G::CE::commit(gens_n, &[G::Scalar::zero()], &r).compress(); // h^r
    alpha.append_to_transcript(b"alpha", transcript);

    let c = G::Scalar::challenge(b"c", transcript);

    let z = c * (*s1 - *s2) + r;

    Ok((Self { alpha, z }, C1, C2))
  }

  pub fn verify(
    &self,
    gens_n: &CommitmentGens<G>,
    transcript: &mut Transcript,
    C1: &CompressedCommitment<G>,
    C2: &CompressedCommitment<G>,
  ) -> Result<(), NovaError> {
    transcript.append_message(b"protocol-name", EqualityProof::<G>::protocol_name());
    C1.append_to_transcript(b"C1", transcript);
    C2.append_to_transcript(b"C2", transcript);
    self.alpha.append_to_transcript(b"alpha", transcript);

    let c = G::Scalar::challenge(b"c", transcript);

    let rhs = {
      let C = C1.decompress()? - C2.decompress()?;
      (C * c + self.alpha.decompress()?).compress()
    };

    let lhs = G::CE::commit(gens_n, &[G::Scalar::zero()], &self.z).compress(); // h^z

    if lhs == rhs {
      Ok(())
    } else {
      Err(NovaError::InvalidEqualityProof)
    }
  }
}

impl<G: Group> ProductProof<G> {
  fn protocol_name() -> &'static [u8] {
    b"product proof"
  }

  pub fn prove(
    gens_n: &CommitmentGens<G>,
    transcript: &mut Transcript,
    x: &G::Scalar,
    rX: &G::Scalar,
    y: &G::Scalar,
    rY: &G::Scalar,
    z: &G::Scalar,
    rZ: &G::Scalar,
  ) -> Result<
    (
      ProductProof<G>,
      CompressedCommitment<G>,
      CompressedCommitment<G>,
      CompressedCommitment<G>,
    ),
    NovaError,
  > {
    transcript.append_message(b"protocol-name", ProductProof::<G>::protocol_name());

    // produce 5 random scalars
    let b1 = G::Scalar::random(&mut OsRng);
    let b2 = G::Scalar::random(&mut OsRng);
    let b3 = G::Scalar::random(&mut OsRng);
    let b4 = G::Scalar::random(&mut OsRng);
    let b5 = G::Scalar::random(&mut OsRng);

    let X = G::CE::commit(gens_n, &[*x], rX).compress();
    X.append_to_transcript(b"X", transcript);

    let Y = G::CE::commit(gens_n, &[*y], rY).compress();
    Y.append_to_transcript(b"Y", transcript);

    let Z = G::CE::commit(gens_n, &[*z], rZ).compress();
    Z.append_to_transcript(b"Z", transcript);

    let alpha = G::CE::commit(gens_n, &[b1], &b2).compress();
    alpha.append_to_transcript(b"alpha", transcript);

    let beta = G::CE::commit(gens_n, &[b3], &b4).compress();
    beta.append_to_transcript(b"beta", transcript);

    let delta = {
      let h_to_b5 = G::CE::commit(gens_n, &[G::Scalar::zero()], &b5); // h^b5
      (X.decompress()? * b3 + h_to_b5).compress() // X^b3*h^b5
    };

    delta.append_to_transcript(b"delta", transcript);

    let c = G::Scalar::challenge(b"c", transcript);

    let z1 = b1 + c * *x;
    let z2 = b2 + c * *rX;
    let z3 = b3 + c * *y;
    let z4 = b4 + c * *rY;
    let z5 = b5 + c * (*rZ - *rX * *y);
    let z = [z1, z2, z3, z4, z5];

    Ok((
      Self {
        alpha,
        beta,
        delta,
        z,
      },
      X,
      Y,
      Z,
    ))
  }

  fn check_equality(
    P: &CompressedCommitment<G>,
    X: &CompressedCommitment<G>,
    c: &G::Scalar,
    gens_n: &CommitmentGens<G>,
    z1: &G::Scalar,
    z2: &G::Scalar,
  ) -> Result<bool, NovaError> {
    let lhs = (P.decompress()? + X.decompress()? * *c).compress();
    let rhs = G::CE::commit(gens_n, &[*z1], z2).compress();

    Ok(lhs == rhs)
  }

  pub fn verify(
    &self,
    gens_n: &CommitmentGens<G>,
    transcript: &mut Transcript,
    X: &CompressedCommitment<G>,
    Y: &CompressedCommitment<G>,
    Z: &CompressedCommitment<G>,
  ) -> Result<(), NovaError> {
    transcript.append_message(b"protocol-name", ProductProof::<G>::protocol_name());

    X.append_to_transcript(b"X", transcript);
    Y.append_to_transcript(b"Y", transcript);
    Z.append_to_transcript(b"Z", transcript);
    self.alpha.append_to_transcript(b"alpha", transcript);
    self.beta.append_to_transcript(b"beta", transcript);
    self.delta.append_to_transcript(b"delta", transcript);

    let z1 = self.z[0];
    let z2 = self.z[1];
    let z3 = self.z[2];
    let z4 = self.z[3];
    let z5 = self.z[4];

    let c = G::Scalar::challenge(b"c", transcript);

    let res = ProductProof::<G>::check_equality(&self.alpha, X, &c, gens_n, &z1, &z2)?
      && ProductProof::<G>::check_equality(&self.beta, Y, &c, gens_n, &z3, &z4)?;

    let res2 = {
      let lhs = (self.delta.decompress()? + Z.decompress()? * c).compress();

      let h_to_z5 = G::CE::commit(gens_n, &[G::Scalar::zero()], &z5); // h^z5
      let rhs = (X.decompress()? * z3 + h_to_z5).compress(); // X^z3*h^z5
      lhs == rhs
    };

    if res && res2 {
      Ok(())
    } else {
      Err(NovaError::InvalidProductProof)
    }
  }
}

impl<G: Group> DotProductProof<G> {
  pub fn protocol_name() -> &'static [u8] {
    b"dot product proof"
  }

  pub fn compute_dotproduct(a: &[G::Scalar], b: &[G::Scalar]) -> G::Scalar {
    assert_eq!(a.len(), b.len());
    let mut result = G::Scalar::zero();

    for i in 0..a.len() {
      result += a[i] * b[i];
    }

    result
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
    transcript.append_message(b"protocol-name", DotProductProof::<G>::protocol_name());

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());
    assert_eq!(gens_n.len(), a_vec.len());
    assert_eq!(gens_1.len(), 1);

    // produce randomness for the proofs
    let d_vec = (0..n)
      .map(|_i| G::Scalar::random(&mut OsRng))
      .collect::<Vec<G::Scalar>>();

    let r_delta = G::Scalar::random(&mut OsRng);
    let r_beta = G::Scalar::random(&mut OsRng);

    let Cx = CE::<G>::commit(gens_n, x_vec, blind_x).compress();
    Cx.append_to_transcript(b"Cx", transcript);

    let Cy = CE::<G>::commit(gens_1, &[*y], blind_y).compress();
    Cy.append_to_transcript(b"Cy", transcript);

    a_vec.append_to_transcript(b"a", transcript);

    let delta = CE::<G>::commit(gens_n, &d_vec, &r_delta).compress();
    delta.append_to_transcript(b"delta", transcript);

    let dotproduct_a_d = DotProductProof::<G>::compute_dotproduct(a_vec, &d_vec);

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
  ) -> Result<(), NovaError> {
    assert_eq!(gens_n.len(), a_vec.len());
    assert_eq!(gens_1.len(), 1);

    transcript.append_message(b"protocol-name", DotProductProof::<G>::protocol_name());

    Cx.append_to_transcript(b"Cx", transcript);
    Cy.append_to_transcript(b"Cy", transcript);
    a_vec.append_to_transcript(b"a", transcript);
    self.delta.append_to_transcript(b"delta", transcript);
    self.beta.append_to_transcript(b"beta", transcript);

    let c = G::Scalar::challenge(b"c", transcript);

    let mut result = Cx.decompress()? * c + self.delta.decompress()?
      == CE::<G>::commit(gens_n, &self.z, &self.z_delta);

    let dotproduct_z_a = DotProductProof::<G>::compute_dotproduct(&self.z, a_vec);
    result &= Cy.decompress()? * c + self.beta.decompress()?
      == CE::<G>::commit(gens_1, &[dotproduct_z_a], &self.z_beta);

    if result {
      Ok(())
    } else {
      Err(NovaError::InvalidDotProductProof)
    }
  }
}
