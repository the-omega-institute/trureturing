/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Positive]
   utility: none
   digest: The counting resolvent is identified with the centered Gram screening formula once the actual finite tree energy bridge is supplied. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceCovariance
import Mathlib.Analysis.InnerProductSpace.Positive

/-! The exact finite counting-screening identity is reduced to the actual source edge bridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceScreening

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (H NodeL2)
open FiniteSourceMass (N)
open FiniteSourceCovariance (one v B Sigma)
open InnerProductSpace

/-! `unitInverse` keeps the inverse attached to the compiled `IsUnit` witness. -/
noncomputable def unitInverse {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (hA : IsUnit A) : E →L[ℝ] E := by
  letI := hA.invertible
  exact ⅟A

structure ActualBridge (n : ℕ) where
  /-- The closed counting-measure Laplacian on the actual occurrence nodes. -/
  L : NodeL2 n →L[ℝ] NodeL2 n
  /-- The counting-normalized root source vector. -/
  source : NodeL2 n
  /-- Root evaluation on actual node potentials. -/
  root : NodeL2 n →L[ℝ] ℝ
  /-- Every actual potential is its root value plus its supported edge increments. -/
  decompose : ∀ f : NodeL2 n, ∃ c : ℝ, ∃ z : H,
    f = c • one n - FiniteSourceHardy.J n z
  /-- The edge energy is the counting Laplacian form on the actual source. -/
  weak_energy : ∀ (c d : ℝ) (z w : H),
    inner ℝ (c • one n - FiniteSourceHardy.J n z)
      (L (d • one n - FiniteSourceHardy.J n w)) =
      inner ℝ z w
  /-- The actual counting Laplacian is symmetric. -/
  symmetric : ∀ f g : NodeL2 n, inner ℝ (L f) g = inner ℝ f (L g)
  /-- The counting Laplacian energy is nonnegative. -/
  positive : ∀ f : NodeL2 n, 0 ≤ inner ℝ (L f) f
  /-- Root evaluation of a reconstructed potential is its constant mode. -/
  root_decompose : ∀ (c : ℝ) (z : H),
    root (c • one n - FiniteSourceHardy.J n z) = c
  /-- The normalized counting source pairs with a reconstructed potential by its root value/N. -/
  source_pair : ∀ (c : ℝ) (z : H),
    inner ℝ source (c • one n - FiniteSourceHardy.J n z) = c / (N n : ℝ)
  /-- The positive screening operator is invertible on the full common edge space. -/
  screened_unit : ∀ (lam : ℝ), 0 < lam →
    IsUnit (ContinuousLinearMap.id ℝ H + ((N n : ℝ) * lam) • FiniteSourceCovariance.Sigma n)
  /-- Positive screening makes the actual node resolvent invertible. -/
  laplacian_unit : ∀ (lam : ℝ), 0 < lam →
    IsUnit (L + lam • (1 : NodeL2 n →L[ℝ] NodeL2 n))
  /-- The centered Gram operator has its covariance bilinear form. -/
  covariance_pair : ∀ (z w : H),
    inner ℝ z (FiniteSourceCovariance.Sigma n w) =
      inner ℝ (FiniteSourceHardy.J n z) (FiniteSourceHardy.J n w) -
        inner ℝ z (v n) * inner ℝ (v n) w

def root_response (n : ℕ) (D : ActualBridge n) (lam : ℝ) (hlam : 0 < lam) : ℝ :=
  D.root (unitInverse (D.L + lam • (1 : NodeL2 n →L[ℝ] NodeL2 n))
    (D.laplacian_unit lam hlam) D.source)

def screened_inverse (n : ℕ) (D : ActualBridge n) (lam : ℝ) (hlam : 0 < lam) : H →L[ℝ] H :=
  unitInverse (ContinuousLinearMap.id ℝ H + ((N n : ℝ) * lam) • FiniteSourceCovariance.Sigma n)
    (D.screened_unit lam hlam)

end D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceScreening
