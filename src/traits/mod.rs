//! This module defines various traits required by the users of the library to implement.
use bellperson::{
  gadgets::{boolean::AllocatedBit, num::AllocatedNum},
  ConstraintSystem, SynthesisError,
};
use core::{
  fmt::Debug,
  ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign},
};
use ff::{PrimeField, PrimeFieldBits};
use merlin::Transcript;
use num_bigint::BigInt;
use serde::{Deserialize, Serialize};

pub mod commitment;

use commitment::CommitmentEngineTrait;

/// Represents an element of a group
/// This is currently tailored for an elliptic curve group
pub trait Group:
  Clone
  + Copy
  + Debug
  + Eq
  + Sized
  + GroupOps
  + GroupOpsOwned
  + ScalarMul<<Self as Group>::Scalar>
  + ScalarMulOwned<<Self as Group>::Scalar>
  + Send
  + Sync
  + Serialize
  + for<'de> Deserialize<'de>
{
  /// A type representing an element of the base field of the group
  type Base: PrimeField + PrimeFieldBits + Serialize + for<'de> Deserialize<'de>;

  /// A type representing an element of the scalar field of the group
  type Scalar: PrimeField
    + PrimeFieldBits
    + ChallengeTrait
    + Send
    + Sync
    + Serialize
    + for<'de> Deserialize<'de>;

  /// A type representing the compressed version of the group element
  type CompressedGroupElement: CompressedGroup<GroupElement = Self>
    + Serialize
    + for<'de> Deserialize<'de>;

  /// A type representing preprocessed group element
  type PreprocessedGroupElement: Clone + Debug + Send + Sync + Serialize + for<'de> Deserialize<'de>;

  /// A type that represents a hash function that consumes elements
  /// from the base field and squeezes out elements of the scalar field
  type RO: ROTrait<Self::Base, Self::Scalar> + Serialize + for<'de> Deserialize<'de>;

  /// An alternate implementation of Self::RO in the circuit model
  type ROCircuit: ROCircuitTrait<Self::Base> + Serialize + for<'de> Deserialize<'de>;

  /// A type that defines a commitment engine over scalars in the group
  type CE: CommitmentEngineTrait<Self> + Serialize + for<'de> Deserialize<'de>;

  /// A method to compute a multiexponentation
  fn vartime_multiscalar_mul(
    scalars: &[Self::Scalar],
    bases: &[Self::PreprocessedGroupElement],
  ) -> Self;

  /// Compresses the group element
  fn compress(&self) -> Self::CompressedGroupElement;

  /// Produces a preprocessed element
  fn preprocessed(&self) -> Self::PreprocessedGroupElement;

  /// Produce a vector of group elements using a static label
  fn from_label(label: &[u8], n: usize) -> Vec<Self::PreprocessedGroupElement>;

  /// Returns the affine coordinates (x, y, infinty) for the point
  fn to_coordinates(&self) -> (Self::Base, Self::Base, bool);

  /// Returns an element that is the additive identity of the group
  fn zero() -> Self;

  /// Returns the generator of the group
  fn get_generator() -> Self;

  /// Returns A, B, and the order of the group as a big integer
  fn get_curve_params() -> (Self::Base, Self::Base, BigInt);
}

/// Represents a compressed version of a group element
pub trait CompressedGroup:
  Clone + Copy + Debug + Eq + Sized + Send + Sync + Serialize + for<'de> Deserialize<'de> + 'static
{
  /// A type that holds the decompressed version of the compressed group element
  type GroupElement: Group + Serialize + for<'de> Deserialize<'de>;

  /// Decompresses the compressed group element
  fn decompress(&self) -> Option<Self::GroupElement>;

  /// Returns a byte array representing the compressed group element
  fn as_bytes(&self) -> &[u8];
}

/// A helper trait to append different types to the transcript
pub trait AppendToTranscriptTrait {
  /// appends the value to the transcript under the provided label
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript);
}

/// A helper trait to absorb different objects in RO
pub trait AbsorbInROTrait<G: Group> {
  /// Absorbs the value in the provided RO
  fn absorb_in_ro(&self, ro: &mut G::RO);
}

/// A helper trait to generate challenges using a transcript object
pub trait ChallengeTrait {
  /// Returns a Scalar representing the challenge using the transcript
  fn challenge(label: &'static [u8], transcript: &mut Transcript) -> Self;
}

/// A helper trait that defines the behavior of a hash function that we use as an RO
pub trait ROTrait<Base, Scalar> {
  /// A type representing constants/parameters associated with the hash function
  type Constants: ROConstantsTrait<Base>
    + Clone
    + Send
    + Sync
    + Serialize
    + for<'de> Deserialize<'de>;

  /// Initializes the hash function
  fn new(constants: Self::Constants, num_absorbs: usize) -> Self;

  /// Adds a scalar to the internal state
  fn absorb(&mut self, e: Base);

  /// Returns a challenge of `num_bits` by hashing the internal state
  fn squeeze(&mut self, num_bits: usize) -> Scalar;
}

/// A helper trait that defines the behavior of a hash function that we use as an RO in the circuit model
pub trait ROCircuitTrait<Base: PrimeField> {
  /// A type representing constants/parameters associated with the hash function
  type Constants: ROConstantsTrait<Base>
    + Clone
    + Send
    + Sync
    + Serialize
    + for<'de> Deserialize<'de>;

  /// Initializes the hash function
  fn new(constants: Self::Constants, num_absorbs: usize) -> Self;

  /// Adds a scalar to the internal state
  fn absorb(&mut self, e: AllocatedNum<Base>);

  /// Returns a challenge of `num_bits` by hashing the internal state
  fn squeeze<CS>(&mut self, cs: CS, num_bits: usize) -> Result<Vec<AllocatedBit>, SynthesisError>
  where
    CS: ConstraintSystem<Base>;
}

/// A helper trait that defines the constants associated with a hash function
pub trait ROConstantsTrait<Base> {
  /// produces constants/parameters associated with the hash function
  fn new() -> Self;
}

/// An alias for constants associated with G::RO
pub type ROConstants<G> =
  <<G as Group>::RO as ROTrait<<G as Group>::Base, <G as Group>::Scalar>>::Constants;

/// An alias for constants associated with G::ROCircuit
pub type ROConstantsCircuit<G> =
  <<G as Group>::ROCircuit as ROCircuitTrait<<G as Group>::Base>>::Constants;

/// A helper trait for types with a group operation.
pub trait GroupOps<Rhs = Self, Output = Self>:
  Add<Rhs, Output = Output> + Sub<Rhs, Output = Output> + AddAssign<Rhs> + SubAssign<Rhs>
{
}

impl<T, Rhs, Output> GroupOps<Rhs, Output> for T where
  T: Add<Rhs, Output = Output> + Sub<Rhs, Output = Output> + AddAssign<Rhs> + SubAssign<Rhs>
{
}

/// A helper trait for references with a group operation.
pub trait GroupOpsOwned<Rhs = Self, Output = Self>: for<'r> GroupOps<&'r Rhs, Output> {}
impl<T, Rhs, Output> GroupOpsOwned<Rhs, Output> for T where T: for<'r> GroupOps<&'r Rhs, Output> {}

/// A helper trait for types implementing group scalar multiplication.
pub trait ScalarMul<Rhs, Output = Self>: Mul<Rhs, Output = Output> + MulAssign<Rhs> {}

impl<T, Rhs, Output> ScalarMul<Rhs, Output> for T where T: Mul<Rhs, Output = Output> + MulAssign<Rhs>
{}

/// A helper trait for references implementing group scalar multiplication.
pub trait ScalarMulOwned<Rhs, Output = Self>: for<'r> ScalarMul<&'r Rhs, Output> {}
impl<T, Rhs, Output> ScalarMulOwned<Rhs, Output> for T where T: for<'r> ScalarMul<&'r Rhs, Output> {}

impl<F: PrimeField> AppendToTranscriptTrait for F {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, self.to_repr().as_ref());
  }
}

impl<F: PrimeField> AppendToTranscriptTrait for [F] {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    for s in self {
      s.append_to_transcript(label, transcript);
    }
  }
}

pub mod circuit;
pub mod evaluation;
pub mod snark;
