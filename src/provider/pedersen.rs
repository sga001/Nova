//! This module provides an implementation of a commitment engine
use crate::{
  errors::NovaError,
  traits::{
    commitment::{
      CommitmentEngineTrait, CommitmentGensTrait, CommitmentTrait, CompressedCommitmentTrait,
    },
    AbsorbInROTrait, AppendToTranscriptTrait, CompressedGroup, Group, ROTrait,
  },
};
use core::{
  fmt::Debug,
  marker::PhantomData,
  ops::{Add, AddAssign, Mul, MulAssign, Sub},
};
use ff::Field;
use merlin::Transcript;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// A type that holds commitment generators
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommitmentGens<G: Group> {
  /// generator vec  
  pub gens: Vec<G::PreprocessedGroupElement>,
  /// temporary public for debug
  pub h: G::PreprocessedGroupElement,
  _p: PhantomData<G>,
}

/// A type that holds a commitment
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct Commitment<G: Group> {
  /// commitment elt
  pub comm: G,
}

/// A type that holds a compressed commitment
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CompressedCommitment<C: CompressedGroup> {
  comm: C,
}

impl<G: Group> CommitmentGensTrait<G> for CommitmentGens<G> {
  type Commitment = Commitment<G>;
  type CompressedCommitment = CompressedCommitment<G::CompressedGroupElement>;

  fn new(label: &'static [u8], n: usize) -> Self {
    let mut blinding_label = label.to_vec();
    blinding_label.extend(b"blinding factor");
    let blinding = G::from_label(&blinding_label, 1);
    let h = blinding.first().unwrap().clone();

    CommitmentGens {
      gens: G::from_label(label, n.next_power_of_two()),
      h,
      _p: Default::default(),
    }
  }

  fn new_exact(label: &'static [u8], n: usize) -> Self {
    let mut blinding_label = label.to_vec();
    blinding_label.extend(b"blinding factor");
    let blinding = G::from_label(&blinding_label, 1);
    let h = blinding.first().unwrap().clone();

    CommitmentGens {
      gens: G::from_label(label, n),
      h,
      _p: Default::default(),
    }
  }

  fn new_with_blinding_gen(
    label: &'static [u8],
    n: usize,
    h: &G::PreprocessedGroupElement,
  ) -> Self {
    CommitmentGens {
      gens: G::from_label(label, n.next_power_of_two()),
      h: h.clone(),
      _p: Default::default(),
    }
  }

  fn new_exact_with_blinding_gen(
    label: &'static [u8],
    n: usize,
    h: &G::PreprocessedGroupElement,
  ) -> Self {
    CommitmentGens {
      gens: G::from_label(label, n),
      h: h.clone(),
      _p: Default::default(),
    }
  }

  fn from_preprocessed(gens: Vec<G::PreprocessedGroupElement>) -> CommitmentGens<G> {
    let h = G::get_generator().preprocessed(); // this is irrelevant since we will not use a blind
    CommitmentGens {
      gens,
      h,
      _p: Default::default(),
    }
  }

  fn len(&self) -> usize {
    self.gens.len()
  }

  fn commit(&self, v: &[G::Scalar], r: &G::Scalar) -> Self::Commitment {
    assert!(self.gens.len() >= v.len());

    let mut scalars: Vec<G::Scalar> = v.to_vec();
    scalars.push(*r);

    let mut bases = self.gens[..v.len()].to_vec();
    bases.push(self.h.clone());

    Self::Commitment {
      comm: G::vartime_multiscalar_mul(&scalars, &bases),
    }
  }

  fn get_gens(&self) -> Vec<G::PreprocessedGroupElement> {
    self.gens.clone()
  }

  fn get_blinding_gen(&self) -> G::PreprocessedGroupElement {
    self.h.clone()
  }
}

impl<G: Group> CommitmentTrait<G> for Commitment<G> {
  type CompressedCommitment = CompressedCommitment<G::CompressedGroupElement>;

  fn compress(&self) -> CompressedCommitment<G::CompressedGroupElement> {
    CompressedCommitment {
      comm: self.comm.compress(),
    }
  }

  fn to_coordinates(&self) -> (G::Base, G::Base, bool) {
    self.comm.to_coordinates()
  }

  fn reinterpret_as_generator(&self) -> G::PreprocessedGroupElement {
    self.comm.preprocessed()
  }
}

impl<G: Group> Default for Commitment<G> {
  fn default() -> Self {
    Commitment { comm: G::zero() }
  }
}

impl<C: CompressedGroup> CompressedCommitmentTrait<C> for CompressedCommitment<C> {
  type Commitment = Commitment<C::GroupElement>;

  fn decompress(&self) -> Result<Self::Commitment, NovaError> {
    let comm = self.comm.decompress();
    if comm.is_none() {
      return Err(NovaError::DecompressionError);
    }
    Ok(Commitment {
      comm: comm.unwrap(),
    })
  }
}

impl<G: Group> AppendToTranscriptTrait for Commitment<G> {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, self.comm.compress().as_bytes());
  }
}

impl<G: Group> AbsorbInROTrait<G> for Commitment<G> {
  fn absorb_in_ro(&self, ro: &mut G::RO) {
    let (x, y, is_infinity) = self.comm.to_coordinates();
    ro.absorb(x);
    ro.absorb(y);
    ro.absorb(if is_infinity {
      G::Base::one()
    } else {
      G::Base::zero()
    });
  }
}

impl<C: CompressedGroup> AppendToTranscriptTrait for CompressedCommitment<C> {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, self.comm.as_bytes());
  }
}

impl<G: Group> MulAssign<G::Scalar> for Commitment<G> {
  fn mul_assign(&mut self, scalar: G::Scalar) {
    let result = (self as &Commitment<G>).comm * scalar;
    *self = Commitment { comm: result };
  }
}

impl<'a, 'b, G: Group> Mul<&'b G::Scalar> for &'a Commitment<G> {
  type Output = Commitment<G>;
  fn mul(self, scalar: &'b G::Scalar) -> Commitment<G> {
    Commitment {
      comm: self.comm * scalar,
    }
  }
}

impl<G: Group> Mul<G::Scalar> for Commitment<G> {
  type Output = Commitment<G>;

  fn mul(self, scalar: G::Scalar) -> Commitment<G> {
    Commitment {
      comm: self.comm * scalar,
    }
  }
}

impl<'b, G: Group> AddAssign<&'b Commitment<G>> for Commitment<G> {
  fn add_assign(&mut self, other: &'b Commitment<G>) {
    let result = (self as &Commitment<G>).comm + other.comm;
    *self = Commitment { comm: result };
  }
}

impl<'a, 'b, G: Group> Add<&'b Commitment<G>> for &'a Commitment<G> {
  type Output = Commitment<G>;
  fn add(self, other: &'b Commitment<G>) -> Commitment<G> {
    Commitment {
      comm: self.comm + other.comm,
    }
  }
}

impl<'a, 'b, G: Group> Sub<&'b Commitment<G>> for &'a Commitment<G> {
  type Output = Commitment<G>;
  fn sub(self, other: &'b Commitment<G>) -> Commitment<G> {
    Commitment {
      comm: self.comm - other.comm,
    }
  }
}

macro_rules! define_add_variants {
  (G = $g:path, LHS = $lhs:ty, RHS = $rhs:ty, Output = $out:ty) => {
    impl<'b, G: $g> Add<&'b $rhs> for $lhs {
      type Output = $out;
      fn add(self, rhs: &'b $rhs) -> $out {
        &self + rhs
      }
    }

    impl<'a, G: $g> Add<$rhs> for &'a $lhs {
      type Output = $out;
      fn add(self, rhs: $rhs) -> $out {
        self + &rhs
      }
    }

    impl<G: $g> Add<$rhs> for $lhs {
      type Output = $out;
      fn add(self, rhs: $rhs) -> $out {
        &self + &rhs
      }
    }
  };
}

macro_rules! define_sub_variants {
  (G = $g:path, LHS = $lhs:ty, RHS = $rhs:ty, Output = $out:ty) => {
    impl<'b, G: $g> Sub<&'b $rhs> for $lhs {
      type Output = $out;
      fn sub(self, rhs: &'b $rhs) -> $out {
        &self - rhs
      }
    }

    impl<'a, G: $g> Sub<$rhs> for &'a $lhs {
      type Output = $out;
      fn sub(self, rhs: $rhs) -> $out {
        self - &rhs
      }
    }

    impl<G: $g> Sub<$rhs> for $lhs {
      type Output = $out;
      fn sub(self, rhs: $rhs) -> $out {
        &self - &rhs
      }
    }
  };
}

macro_rules! define_add_assign_variants {
  (G = $g:path, LHS = $lhs:ty, RHS = $rhs:ty) => {
    impl<G: $g> AddAssign<$rhs> for $lhs {
      fn add_assign(&mut self, rhs: $rhs) {
        *self += &rhs;
      }
    }
  };
}

define_add_assign_variants!(G = Group, LHS = Commitment<G>, RHS = Commitment<G>);
define_add_variants!(G = Group, LHS = Commitment<G>, RHS = Commitment<G>, Output = Commitment<G>);
define_sub_variants!(G = Group, LHS = Commitment<G>, RHS = Commitment<G>, Output = Commitment<G>);

/// Provides a commitment engine
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommitmentEngine<G: Group> {
  _p: PhantomData<G>,
}

impl<G: Group> CommitmentEngineTrait<G> for CommitmentEngine<G> {
  type CommitmentGens = CommitmentGens<G>;
  type Commitment = Commitment<G>;
  type CompressedCommitment = CompressedCommitment<G::CompressedGroupElement>;

  fn commit(gens: &Self::CommitmentGens, v: &[G::Scalar], r: &G::Scalar) -> Self::Commitment {
    gens.commit(v, r)
  }
}

/// trait for commitment generation
pub trait CommitmentGensExtTrait<G: Group>: CommitmentGensTrait<G> {
  /// commitment engine trait
  type CE: CommitmentEngineTrait<G>;

  /// Splits the commitment key into two pieces at a specified point
  fn split_at(&self, n: usize) -> (Self, Self)
  where
    Self: Sized;

  /// Combines two commitment keys into one
  fn combine(&self, other: &Self) -> Self;

  /// Folds the two commitment keys into one using the provided weights
  fn fold(&self, w1: &G::Scalar, w2: &G::Scalar) -> Self;

  /// Scales the commitment key using the provided scalar
  fn scale(&self, r: &G::Scalar) -> Self;
}

impl<G: Group> CommitmentGensExtTrait<G> for CommitmentGens<G> {
  type CE = CommitmentEngine<G>;

  fn split_at(&self, n: usize) -> (CommitmentGens<G>, CommitmentGens<G>) {
    (
      CommitmentGens {
        gens: self.gens[0..n].to_vec(),
        h: self.h.clone(),
        _p: Default::default(),
      },
      CommitmentGens {
        gens: self.gens[n..].to_vec(),
        h: self.h.clone(),
        _p: Default::default(),
      },
    )
  }

  fn combine(&self, other: &CommitmentGens<G>) -> CommitmentGens<G> {
    let gens = {
      let mut c = self.gens.clone();
      c.extend(other.gens.clone());
      c
    };
    CommitmentGens {
      gens,
      h: self.h.clone(),
      _p: Default::default(),
    }
  }

  // combines the left and right halves of `self` using `w1` and `w2` as the weights
  fn fold(&self, w1: &G::Scalar, w2: &G::Scalar) -> CommitmentGens<G> {
    let w = vec![*w1, *w2];
    let (L, R) = self.split_at(self.len() / 2);

    let gens = (0..self.len() / 2)
      .into_par_iter()
      .map(|i| {
        let bases = [L.gens[i].clone(), R.gens[i].clone()].to_vec();
        G::vartime_multiscalar_mul(&w, &bases).preprocessed()
      })
      .collect();

    CommitmentGens {
      gens,
      h: self.h.clone(),
      _p: Default::default(),
    }
  }

  /// Scales each element in `self` by `r`
  fn scale(&self, r: &G::Scalar) -> Self {
    let gens_scaled = self
      .gens
      .clone()
      .into_par_iter()
      .map(|g| G::vartime_multiscalar_mul(&[*r], &[g]).preprocessed())
      .collect();

    CommitmentGens {
      gens: gens_scaled,
      h: self.h.clone(),
      _p: Default::default(),
    }
  }
}
