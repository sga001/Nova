//! This module defines basic types related to polynomials
use core::ops::Index;
use ff::PrimeField;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// Polynomial struct
pub struct EqPolynomial<Scalar: PrimeField> {
  r: Vec<Scalar>,
}

impl<Scalar: PrimeField> EqPolynomial<Scalar> {
  /// Creates a new polynomial from its succinct specification
  pub fn new(r: Vec<Scalar>) -> Self {
    EqPolynomial { r }
  }

  /// Evaluates the polynomial at the specified point
  pub fn evaluate(&self, rx: &[Scalar]) -> Scalar {
    assert_eq!(self.r.len(), rx.len());
    (0..rx.len())
      .map(|i| rx[i] * self.r[i] + (Scalar::one() - rx[i]) * (Scalar::one() - self.r[i]))
      .fold(Scalar::one(), |acc, item| acc * item)
  }

  /// evals
  pub fn evals(&self) -> Vec<Scalar> {
    let ell = self.r.len();
    let mut evals: Vec<Scalar> = vec![Scalar::zero(); (2_usize).pow(ell as u32)];
    let mut size = 1;
    evals[0] = Scalar::one();

    for r in self.r.iter().rev() {
      let (evals_left, evals_right) = evals.split_at_mut(size);
      let (evals_right, _) = evals_right.split_at_mut(size);

      evals_left
        .par_iter_mut()
        .zip(evals_right.par_iter_mut())
        .for_each(|(x, y)| {
          *y = *x * r;
          *x -= &*y;
        });

      size *= 2;
    }
    evals
  }

  /// factored lens
  pub fn compute_factored_lens(ell: usize) -> (usize, usize) {
    (ell / 2, ell - ell / 2)
  }

  /// factored evals
  pub fn compute_factored_evals(&self) -> (Vec<Scalar>, Vec<Scalar>) {
    let ell = self.r.len();
    let (left_num_vars, _right_num_vars) = EqPolynomial::<Scalar>::compute_factored_lens(ell);

    let L = EqPolynomial::new(self.r[..left_num_vars].to_vec()).evals();
    let R = EqPolynomial::new(self.r[left_num_vars..ell].to_vec()).evals();

    (L, R)
  }
}

#[derive(Debug, Serialize, Deserialize)]
/// A multilinear polynomial with num_vars and 2^num_vars entries
pub struct MultilinearPolynomial<Scalar: PrimeField> {
  num_vars: usize, // the number of variables in the multilinear polynomial
  Z: Vec<Scalar>,  // evaluations of the polynomial in all the 2^num_vars Boolean inputs
}

impl<Scalar: PrimeField> MultilinearPolynomial<Scalar> {
  /// Creates a new multilinear polynomial from a vector of scalars
  /// representing the evaluations of the polynomial
  pub fn new(Z: Vec<Scalar>) -> Self {
    assert_eq!(Z.len(), (2_usize).pow((Z.len() as f64).log2() as u32));
    MultilinearPolynomial {
      num_vars: (Z.len() as f64).log2() as usize,
      Z,
    }
  }

  /// Returns the number of variables
  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }

  /// Returns the underlying vector of scalars
  pub fn get_Z(&self) -> &[Scalar] {
    &self.Z
  }

  /// Returns the length of the polynomial
  pub fn len(&self) -> usize {
    self.Z.len()
  }

  /// Returns whether polynomial is empty
  pub fn is_empty(&self) -> bool {
    self.Z.len() == 0
  }

  /// TBD
  pub fn bound(&self, L: &[Scalar]) -> Vec<Scalar> {
    let (left_num_vars, right_num_vars) =
      EqPolynomial::<Scalar>::compute_factored_lens(self.num_vars);
    let L_size = (2_usize).pow(left_num_vars as u32);
    let R_size = (2_usize).pow(right_num_vars as u32);

    (0..R_size)
      .map(|i| {
        (0..L_size)
          .map(|j| L[j] * self.Z[j * R_size + i])
          .fold(Scalar::zero(), |x, y| x + y)
      })
      .collect()
  }

  /// TBD
  pub fn bound_poly_var_top(&mut self, r: &Scalar) {
    let n = self.len() / 2;

    let (left, right) = self.Z.split_at_mut(n);
    let (right, _) = right.split_at(n);

    left
      .par_iter_mut()
      .zip(right.par_iter())
      .for_each(|(a, b)| {
        *a += *r * (*b - *a);
      });

    self.Z.resize(n, Scalar::zero());
    self.num_vars -= 1;
  }

  /// Returns Z(r) in O(n) time
  pub fn evaluate(&self, r: &[Scalar]) -> Scalar {
    // r must have a value for each variable
    assert_eq!(r.len(), self.get_num_vars());
    let chis = EqPolynomial::new(r.to_vec()).evals();
    assert_eq!(chis.len(), self.Z.len());

    (0..chis.len())
      .into_par_iter()
      .map(|i| chis[i] * self.Z[i])
      .reduce(Scalar::zero, |x, y| x + y)
  }
}

impl<Scalar: PrimeField> Index<usize> for MultilinearPolynomial<Scalar> {
  type Output = Scalar;

  #[inline(always)]
  fn index(&self, _index: usize) -> &Scalar {
    &(self.Z[_index])
  }
}

pub(crate) struct SparsePolynomial<Scalar: PrimeField> {
  num_vars: usize,
  Z: Vec<(usize, Scalar)>,
}

impl<Scalar: PrimeField> SparsePolynomial<Scalar> {
  pub fn new(num_vars: usize, Z: Vec<(usize, Scalar)>) -> Self {
    SparsePolynomial { num_vars, Z }
  }

  fn compute_chi(a: &[bool], r: &[Scalar]) -> Scalar {
    assert_eq!(a.len(), r.len());
    let mut chi_i = Scalar::one();
    for j in 0..r.len() {
      if a[j] {
        chi_i *= r[j];
      } else {
        chi_i *= Scalar::one() - r[j];
      }
    }
    chi_i
  }

  // Takes O(n log n). TODO: do this in O(n) where n is the number of entries in Z
  pub fn evaluate(&self, r: &[Scalar]) -> Scalar {
    assert_eq!(self.num_vars, r.len());

    let get_bits = |num: usize, num_bits: usize| -> Vec<bool> {
      (0..num_bits)
        .into_par_iter()
        .map(|shift_amount| ((num & (1 << (num_bits - shift_amount - 1))) > 0))
        .collect::<Vec<bool>>()
    };

    (0..self.Z.len())
      .into_par_iter()
      .map(|i| {
        let bits = get_bits(self.Z[i].0, r.len());
        SparsePolynomial::compute_chi(&bits, r) * self.Z[i].1
      })
      .reduce(Scalar::zero, |x, y| x + y)
  }
}
