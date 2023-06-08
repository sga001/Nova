//! This module defines a collection of traits that define the behavior of a polynomial evaluation engine
//! A vector of size N is treated as a multilinear polynomial in \log{N} variables,
//! and a commitment provided by the commitment engine is treated as a multilinear polynomial commitment
use crate::{
  errors::NovaError,
  traits::{commitment::CommitmentEngineTrait, Group},
};
use merlin::Transcript;
use serde::{Deserialize, Serialize};

/// A trait that returns commitment of an evaluation argument
pub trait GetEvalCommitmentsTrait<G: Group> {
  /// Returns the commitment at index
  fn get_eval_commitment(
    &self,
    index: usize,
  ) -> <G::CE as CommitmentEngineTrait<G>>::CompressedCommitment;
}

/// A trait that returns the generators
pub trait GetGeneratorsTrait<G: Group> {
  /// Return the vector generators
  fn get_vector_gen(&self) -> &<G::CE as CommitmentEngineTrait<G>>::CommitmentGens;
  /// Return the scalar generator
  fn get_scalar_gen(&self) -> &<G::CE as CommitmentEngineTrait<G>>::CommitmentGens;
}

/// A trait that ties different pieces of the commitment evaluation together
pub trait EvaluationEngineTrait<G: Group>:
  Clone + Send + Sync + Serialize + for<'de> Deserialize<'de>
{
  /// A type that holds the associated commitment engine
  type CE: CommitmentEngineTrait<G>;

  /// A type that holds generators
  type EvaluationGens: Clone
    + Send
    + Sync
    + Serialize
    + for<'de> Deserialize<'de>
    + GetGeneratorsTrait<G>;

  /// A type that holds the evaluation argument
  type EvaluationArgument: Clone
    + Send
    + Sync
    + Serialize
    + for<'de> Deserialize<'de>
    + GetEvalCommitmentsTrait<G>;

  /// A method to perform any additional setup needed to produce proofs of evaluations
  fn setup(gens: &<Self::CE as CommitmentEngineTrait<G>>::CommitmentGens) -> Self::EvaluationGens;

  /// A method to prove evaluations of a batch of polynomials
  #[allow(clippy::too_many_arguments)]
  fn prove_batch(
    gens: &Self::EvaluationGens,
    transcript: &mut Transcript,
    comm: &[<Self::CE as CommitmentEngineTrait<G>>::Commitment],
    polys: &[Vec<G::Scalar>],
    blinds_polys: &[G::Scalar],
    points: &[Vec<G::Scalar>],
    evals: &[G::Scalar],
    blinds_evals: &[G::Scalar],
    comm_evals: &[<Self::CE as CommitmentEngineTrait<G>>::CompressedCommitment],
  ) -> Result<Self::EvaluationArgument, NovaError>;

  /// A method to verify purported evaluations of a batch of polynomials
  fn verify_batch(
    gens: &Self::EvaluationGens,
    transcript: &mut Transcript,
    comm: &[<Self::CE as CommitmentEngineTrait<G>>::Commitment],
    points: &[Vec<G::Scalar>],
    arg: &Self::EvaluationArgument,
  ) -> Result<(), NovaError>;
}
