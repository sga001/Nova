//! This module defines a collection of traits that define the behavior of a commitment engine
//! We require the commitment engine to provide a commitment to vectors with a single group element
use crate::{
  errors::NovaError,
  traits::{AbsorbInROTrait, AppendToTranscriptTrait, CompressedGroup, Group},
};
use core::{
  fmt::Debug,
  ops::{Add, AddAssign, Mul, MulAssign, Sub},
};
use serde::{Deserialize, Serialize};

/// This trait defines the behavior of commitment key
#[allow(clippy::len_without_is_empty)]
pub trait CommitmentGensTrait<G: Group>:
  Clone + Debug + Send + Sync + Serialize + for<'de> Deserialize<'de>
{
  /// Holds the type of the commitment that can be produced
  type Commitment;

  /// Holds the type of the compressed commitment
  type CompressedCommitment;

  /// Samples a new commitment generator of a specified size (power of 2)
  fn new(label: &'static [u8], n: usize) -> Self;

  /// Samples a new commitment generator of a specified size
  fn new_exact(label: &'static [u8], n: usize) -> Self;

  /// Samples a new commitment generator (power of 2) but reuses an existing blinding generator
  fn new_with_blinding_gen(label: &'static [u8], n: usize, h: &G::PreprocessedGroupElement)
    -> Self;

  /// Samples a new commitment generator of specific size but reuses an existing blinding generator
  fn new_exact_with_blinding_gen(
    label: &'static [u8],
    n: usize,
    h: &G::PreprocessedGroupElement,
  ) -> Self;

  /// Returns the vector length that can be committed
  fn len(&self) -> usize;

  /// Commits to a vector using the commitment key
  fn commit(&self, v: &[G::Scalar], r: &G::Scalar) -> Self::Commitment;

  /// Returns the generators of the commitment
  fn get_gens(&self) -> Vec<G::PreprocessedGroupElement>;

  /// Returns the blinding generator of the commitment
  fn get_blinding_gen(&self) -> G::PreprocessedGroupElement;
}

/// Defines basic operations on commitments
pub trait CommitmentOps<Rhs = Self, Output = Self>:
  Add<Rhs, Output = Output> + AddAssign<Rhs> + Sub<Rhs, Output = Output>
{
}

impl<T, Rhs, Output> CommitmentOps<Rhs, Output> for T where
  T: Add<Rhs, Output = Output> + AddAssign<Rhs> + Sub<Rhs, Output = Output>
{
}

/// A helper trait for references with a commitment operation
pub trait CommitmentOpsOwned<Rhs = Self, Output = Self>:
  for<'r> CommitmentOps<&'r Rhs, Output>
{
}
impl<T, Rhs, Output> CommitmentOpsOwned<Rhs, Output> for T where
  T: for<'r> CommitmentOps<&'r Rhs, Output>
{
}

/// A helper trait for types implementing a multiplication of a commitment with a scalar
pub trait ScalarMul<Rhs, Output = Self>: Mul<Rhs, Output = Output> + MulAssign<Rhs> {}

impl<T, Rhs, Output> ScalarMul<Rhs, Output> for T where T: Mul<Rhs, Output = Output> + MulAssign<Rhs>
{}

/// This trait defines the behavior of the commitment
pub trait CommitmentTrait<G: Group>:
  Clone
  + Copy
  + Debug
  + Default
  + PartialEq
  + Eq
  + Send
  + Sync
  + Serialize
  + for<'de> Deserialize<'de>
  + AbsorbInROTrait<G>
  + AppendToTranscriptTrait
  + CommitmentOps
  + CommitmentOpsOwned
  + ScalarMul<G::Scalar>
{
  /// Holds the type of the compressed commitment
  type CompressedCommitment;

  /// Compresses self into a compressed commitment
  fn compress(&self) -> Self::CompressedCommitment;

  /// Returns the coordinate representation of the commitment
  fn to_coordinates(&self) -> (G::Base, G::Base, bool);
}

/// This trait defines the behavior of a compressed commitment
pub trait CompressedCommitmentTrait<C: CompressedGroup>:
  Clone
  + Debug
  + PartialEq
  + Eq
  + Send
  + Sync
  + Serialize
  + for<'de> Deserialize<'de>
  + AppendToTranscriptTrait
{
  /// Holds the type of the commitment that can be decompressed into
  type Commitment;

  /// Decompresses self into a commitment
  fn decompress(&self) -> Result<Self::Commitment, NovaError>;
}

/// A trait that ties different pieces of the commitment generation together
pub trait CommitmentEngineTrait<G: Group>:
  Clone + Send + Sync + Serialize + for<'de> Deserialize<'de>
{
  /// Holds the type of the commitment key
  type CommitmentGens: CommitmentGensTrait<
    G,
    Commitment = Self::Commitment,
    CompressedCommitment = Self::CompressedCommitment,
  >;

  /// Holds the type of the commitment
  type Commitment: CommitmentTrait<G, CompressedCommitment = Self::CompressedCommitment>;

  /// Holds the type of the compressed commitment
  type CompressedCommitment: CompressedCommitmentTrait<
    G::CompressedGroupElement,
    Commitment = Self::Commitment,
  >;

  /// Commits to the provided vector using the provided generators
  fn commit(gens: &Self::CommitmentGens, v: &[G::Scalar], r: &G::Scalar) -> Self::Commitment;
}
