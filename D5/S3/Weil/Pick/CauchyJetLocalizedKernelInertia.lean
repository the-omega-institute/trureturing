/- GID: D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/CauchyJetLocalizedKernelInertia
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A distinct signed-support Cauchy-jet sampling has negative index exactly equal to the active reflected-orbit barcode count. -/

import D5.S3.Analytic.GoldenTomography.CauchyFeatureRightInverse
import D5.S3.Weil.Pick.DiagonalSignNegativeIndex
import D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback
import D5.S3.Weil.Pick.ObserverSignedSupportBarcode
import Mathlib.Tactic

/-!
# Cauchy-jet localized-kernel inertia

This node closes the finite algebraic chain:

* observer-dependent signed support gives localized real weights;
* distinct support coordinates give an invertible Cauchy-jet feature matrix;
* invertible Hermitian congruence preserves inertia;
* diagonal inertia counts weight signs;
* positive masses identify negative weights with active reflected-orbit
  intervals.

The conclusion is exact for the finite square Cauchy-jet sampling scheme. It
does not construct a completed-xi Stieltjes representation, control infinite
tails, realize a Weil test function, or prove RH.
-/

/- Library-first audit trail (2026-09-03):
   * `CauchyFeatureRightInverse` owns the reciprocal-node Vandermonde
     factorization, nonsingular determinant, and canonical two-sided inverse.
   * `InvertibleHermitianInertiaPullback` owns exact inertia preservation under
     an invertible square congruence.
   * `DiagonalSignNegativeIndex` owns exact sign-count inertia for real
     diagonal Hermitian forms.
   * `ObserverSignedSupportBarcode` owns the equivalence between negative
     signed support, negative localized weight under positive mass, and active
     orbit intervals.
   * This node only assembles those owners. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace D5.S3.Weil.Pick.CauchyJetLocalizedKernelInertia

open RHLinalg
open D5.S3.Analytic.GoldenTomography.CauchyFeatureRightInverse
open D5.S3.Weil.Pick.DiagonalSignNegativeIndex
open D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback
open D5.S3.Weil.Pick.ObserverSignedSupportBarcode

/-- The finite observer-dependent signed-support profile. -/
def observerSupportProfile {n : ℕ}
    (delta gamma : Fin n → ℝ) (time : ℝ) : Fin n → ℝ :=
  fun a => observerSignedSupport (delta a) (gamma a) time

/-- The same support profile embedded in the complex plane. -/
def observerSupportComplex {n : ℕ}
    (delta gamma : Fin n → ℝ) (time : ℝ) : Fin n → ℂ :=
  fun a => (observerSupportProfile delta gamma time a : ℂ)

/-- Positive mass times observer-dependent signed support. -/
def observerLocalizedWeightProfile {n : ℕ}
    (mass delta gamma : Fin n → ℝ) (time : ℝ) : Fin n → ℝ :=
  fun a => observerLocalizedWeight
    (mass a) (delta a) (gamma a) time

/-- The canonical square Cauchy-jet feature matrix, sampled one imaginary unit
away from the real signed-support axis. -/
def observerCauchyJetFeatureMatrix {n : ℕ}
    (delta gamma : Fin n → ℝ) (time : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  cauchyJetFeatureMatrix
    (observerSupportComplex delta gamma time) Complex.I

/-- The localized finite Gram matrix. -/
def observerLocalizedCauchyJetGram {n : ℕ}
    (mass delta gamma : Fin n → ℝ) (time : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (observerCauchyJetFeatureMatrix delta gamma time)ᴴ *
    realDiagonal (observerLocalizedWeightProfile mass delta gamma time) *
    observerCauchyJetFeatureMatrix delta gamma time

/-- The localized Gram matrix is Hermitian. -/
def observerLocalizedCauchyJetGramIsHermitian {n : ℕ}
    (mass delta gamma : Fin n → ℝ) (time : ℝ) :
    (observerLocalizedCauchyJetGram mass delta gamma time).IsHermitian :=
  isHermitian_conjTranspose_mul_mul
    (observerCauchyJetFeatureMatrix delta gamma time)
    (real_diagonal_isHermitian
      (observerLocalizedWeightProfile mass delta gamma time))

/-- Injectivity of real signed supports passes to their complex embedding. -/
private theorem observer_support_complex_injective {n : ℕ}
    (delta gamma : Fin n → ℝ) (time : ℝ)
    (hSupport :
      Function.Injective (observerSupportProfile delta gamma time)) :
    Function.Injective (observerSupportComplex delta gamma time) := by
  intro a b hEqual
  apply hSupport
  have hReal := congrArg Complex.re hEqual
  simpa [observerSupportComplex] using hReal

/-- Every real signed-support coordinate avoids the canonical center `i`. -/
private theorem observer_support_complex_avoids_I {n : ℕ}
    (delta gamma : Fin n → ℝ) (time : ℝ) (a : Fin n) :
    observerSupportComplex delta gamma time a ≠ Complex.I := by
  intro hEqual
  have hImag : (0 : ℝ) = 1 := by
    simpa [observerSupportComplex] using congrArg Complex.im hEqual
  norm_num at hImag

/-- Distinct signed supports make the canonical observer Cauchy-jet feature
matrix nonsingular. -/
private theorem observer_cauchy_jet_feature_det_ne_zero {n : ℕ}
    (delta gamma : Fin n → ℝ) (time : ℝ)
    (hSupport :
      Function.Injective (observerSupportProfile delta gamma time)) :
    Matrix.det (observerCauchyJetFeatureMatrix delta gamma time) ≠ 0 := by
  apply cauchy_jet_feature_det_ne_zero
  · exact observer_support_complex_injective delta gamma time hSupport
  · exact observer_support_complex_avoids_I delta gamma time

/-- The canonical observer Cauchy-jet inverse is a two-sided inverse. -/
private theorem observer_cauchy_jet_feature_inverse {n : ℕ}
    (delta gamma : Fin n → ℝ) (time : ℝ)
    (hSupport :
      Function.Injective (observerSupportProfile delta gamma time)) :
    observerCauchyJetFeatureMatrix delta gamma time *
        cauchyJetFeatureRightInverse
          (observerSupportComplex delta gamma time) Complex.I = 1 ∧
      cauchyJetFeatureRightInverse
          (observerSupportComplex delta gamma time) Complex.I *
        observerCauchyJetFeatureMatrix delta gamma time = 1 := by
  constructor
  · exact cauchy_jet_feature_mul_rightInverse
      (observer_support_complex_injective delta gamma time hSupport)
      (observer_support_complex_avoids_I delta gamma time)
  · exact cauchy_jet_feature_rightInverse_mul
      (observer_support_complex_injective delta gamma time hSupport)
      (observer_support_complex_avoids_I delta gamma time)

/-- The localized Cauchy-jet Gram matrix has exactly the same positive and
negative indices as its signed diagonal weight matrix. -/
private theorem observer_localized_cauchy_jet_inertia_eq_sign_counts {n : ℕ}
    (mass delta gamma : Fin n → ℝ) (time : ℝ)
    (hSupport :
      Function.Injective (observerSupportProfile delta gamma time)) :
    posIndex
        (observerLocalizedCauchyJetGramIsHermitian
          mass delta gamma time) =
        positiveWeightCount
          (observerLocalizedWeightProfile mass delta gamma time) ∧
      negIndex
        (observerLocalizedCauchyJetGramIsHermitian
          mass delta gamma time) =
        negativeWeightCount
          (observerLocalizedWeightProfile mass delta gamma time) := by
  have hFeature :
      IsUnit (Matrix.det
        (observerCauchyJetFeatureMatrix delta gamma time)) :=
    isUnit_iff_ne_zero.mpr
      (observer_cauchy_jet_feature_det_ne_zero
        delta gamma time hSupport)
  have hInertia :=
    inertia_invariant_of_isUnit_det
      (real_diagonal_isHermitian
        (observerLocalizedWeightProfile mass delta gamma time))
      (observerCauchyJetFeatureMatrix delta gamma time)
      hFeature
  have hSigns :=
    real_diagonal_inertia_eq_sign_counts
      (observerLocalizedWeightProfile mass delta gamma time)
  constructor
  · calc
      posIndex
          (observerLocalizedCauchyJetGramIsHermitian
            mass delta gamma time) =
        posIndex
          (real_diagonal_isHermitian
            (observerLocalizedWeightProfile mass delta gamma time)) := by
              simpa [observerLocalizedCauchyJetGramIsHermitian,
                observerLocalizedCauchyJetGram] using hInertia.1
      _ = positiveWeightCount
          (observerLocalizedWeightProfile mass delta gamma time) :=
        hSigns.1
  · calc
      negIndex
          (observerLocalizedCauchyJetGramIsHermitian
            mass delta gamma time) =
        negIndex
          (real_diagonal_isHermitian
            (observerLocalizedWeightProfile mass delta gamma time)) := by
              simpa [observerLocalizedCauchyJetGramIsHermitian,
                observerLocalizedCauchyJetGram] using hInertia.2
      _ = negativeWeightCount
          (observerLocalizedWeightProfile mass delta gamma time) :=
        hSigns.2

/-- Under positive masses, the sampled localized Gram negative index is exactly
the number of active reflected-orbit intervals. -/
private theorem observer_localized_cauchy_jet_negIndex_eq_activeOrbitCount {n : ℕ}
    (mass delta gamma : Fin n → ℝ) (time : ℝ)
    (hmass : ∀ a, 0 < mass a)
    (hSupport :
      Function.Injective (observerSupportProfile delta gamma time)) :
    negIndex
        (observerLocalizedCauchyJetGramIsHermitian
          mass delta gamma time) =
      activeOrbitCount delta gamma time := by
  calc
    negIndex
        (observerLocalizedCauchyJetGramIsHermitian
          mass delta gamma time) =
      negativeWeightCount
        (observerLocalizedWeightProfile mass delta gamma time) :=
      (observer_localized_cauchy_jet_inertia_eq_sign_counts
        mass delta gamma time hSupport).2
    _ = negativeLocalizedWeightCount mass delta gamma time := by
      rfl
    _ = activeOrbitCount delta gamma time :=
      negative_localized_weight_count_eq_active_orbit_count
        mass delta gamma time hmass

/-- The sampled localized Gram has a negative direction exactly when at least
one reflected orbit is active. -/
private theorem observer_localized_cauchy_jet_negIndex_pos_iff_exists_active {n : ℕ}
    (mass delta gamma : Fin n → ℝ) (time : ℝ)
    (hmass : ∀ a, 0 < mass a)
    (hSupport :
      Function.Injective (observerSupportProfile delta gamma time)) :
    0 <
        negIndex
          (observerLocalizedCauchyJetGramIsHermitian
            mass delta gamma time) ↔
      ∃ a, orbitActiveAt (delta a) (gamma a) time := by
  rw [observer_localized_cauchy_jet_negIndex_eq_activeOrbitCount
    mass delta gamma time hmass hSupport]
  simp [activeOrbitCount]

/-- Vanishing sampled negative index is equivalent to absence of every active
reflected-orbit interval. -/
private theorem observer_localized_cauchy_jet_negIndex_eq_zero_iff_no_active {n : ℕ}
    (mass delta gamma : Fin n → ℝ) (time : ℝ)
    (hmass : ∀ a, 0 < mass a)
    (hSupport :
      Function.Injective (observerSupportProfile delta gamma time)) :
    negIndex
        (observerLocalizedCauchyJetGramIsHermitian
          mass delta gamma time) = 0 ↔
      ∀ a, ¬ orbitActiveAt (delta a) (gamma a) time := by
  rw [observer_localized_cauchy_jet_negIndex_eq_activeOrbitCount
    mass delta gamma time hmass hSupport]
  simp [activeOrbitCount]

/-- The complete finite chain, packaged for downstream consumers. -/
theorem cauchy_jet_localized_kernel_barcode_inertia {n : ℕ}
    (mass delta gamma : Fin n → ℝ) (time : ℝ)
    (hmass : ∀ a, 0 < mass a)
    (hSupport :
      Function.Injective (observerSupportProfile delta gamma time)) :
    negIndex
        (observerLocalizedCauchyJetGramIsHermitian
          mass delta gamma time) =
        activeOrbitCount delta gamma time ∧
      (0 <
          negIndex
            (observerLocalizedCauchyJetGramIsHermitian
              mass delta gamma time) ↔
        ∃ a, orbitActiveAt (delta a) (gamma a) time) ∧
      (negIndex
          (observerLocalizedCauchyJetGramIsHermitian
            mass delta gamma time) = 0 ↔
        ∀ a, ¬ orbitActiveAt (delta a) (gamma a) time) := by
  exact ⟨
    observer_localized_cauchy_jet_negIndex_eq_activeOrbitCount
      mass delta gamma time hmass hSupport,
    observer_localized_cauchy_jet_negIndex_pos_iff_exists_active
      mass delta gamma time hmass hSupport,
    observer_localized_cauchy_jet_negIndex_eq_zero_iff_no_active
      mass delta gamma time hmass hSupport⟩

#print axioms cauchy_jet_localized_kernel_barcode_inertia

end D5.S3.Weil.Pick.CauchyJetLocalizedKernelInertia
