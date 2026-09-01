/- GID: D5/S3/SpectralTopology/FiniteLocalizerIndex
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/FiniteLocalizerIndex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hermitian spectral localizers inherit finite positive, negative, and signed inertia indices with exact sign-pattern invariance. -/

import D5.S3.SpectralTopology.FinitePointGapLocalizer
import D5.S3.Weil.ZetaLinear.PosIndex
import Mathlib.Tactic

/-!
# Finite localizer inertia index

Every finite Hermitian localizer has positive and negative inertia counts.  The
signed localizer index is their integer difference.  It depends only on the
sign pattern of the Hermitian eigenvalues, so any deformation preserving that
pattern preserves the index.  Conversely, an index change forces some
positive or negative spectral sign classification to change.

This is the finite inertia interface required by spectral-localizer topology.
A norm-open perturbation theorem still requires quantitative eigenvalue
continuity and a proved localizer gap; it is not asserted by this file.
-/

/- Library-search audit trail (2026-09-01):
   * `FiniteHermitianLocalizer` owns the Hermitian block matrix.
   * `FinitePointGapLocalizer` owns an explicit finite invertibility result.
   * `RHLinalg.PosIndex` owns the repository-standard positive and negative
     Hermitian inertia counts.  They are reused directly.
   * Repository search found no localizer specialization or signed inertia
     interface. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.SpectralTopology.FiniteLocalizerIndex

open D5.S3.SpectralTopology.FiniteHermitianLocalizer
open RHLinalg

noncomputable section

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Negative inertia index of a finite Hermitian spectral localizer. -/
def finiteLocalizerNegativeIndex
    (kappa x : ℝ) (X H : Matrix n n ℂ) (z : ℂ)
    (hX : X.IsHermitian) : ℕ :=
  negIndex (finiteHermitianLocalizer_isHermitian kappa x hX H z)

/-- Positive inertia index of a finite Hermitian spectral localizer. -/
def finiteLocalizerPositiveIndex
    (kappa x : ℝ) (X H : Matrix n n ℂ) (z : ℂ)
    (hX : X.IsHermitian) : ℕ :=
  posIndex (finiteHermitianLocalizer_isHermitian kappa x hX H z)

/-- Signed finite localizer inertia index. -/
def finiteLocalizerSignedIndex
    (kappa x : ℝ) (X H : Matrix n n ℂ) (z : ℂ)
    (hX : X.IsHermitian) : ℤ :=
  (finiteLocalizerPositiveIndex kappa x X H z hX : ℤ) -
    (finiteLocalizerNegativeIndex kappa x X H z hX : ℤ)

/-- Two Hermitian matrices have the same spectral sign pattern. -/
def SameHermitianSignPattern
    {index : Type*} [Fintype index]
    {first second : Matrix index index ℂ}
    (hFirst : first.IsHermitian) (hSecond : second.IsHermitian) : Prop :=
  (∀ i, hFirst.eigenvalues i < 0 ↔ hSecond.eigenvalues i < 0) ∧
    (∀ i, 0 < hFirst.eigenvalues i ↔ 0 < hSecond.eigenvalues i)

/-- Negative inertia depends only on the negative eigenvalue sign pattern. -/
theorem negIndex_eq_of_same_negative_pattern
    {index : Type*} [Fintype index]
    {first second : Matrix index index ℂ}
    (hFirst : first.IsHermitian) (hSecond : second.IsHermitian)
    (hPattern : ∀ i,
      hFirst.eigenvalues i < 0 ↔ hSecond.eigenvalues i < 0) :
    negIndex hFirst = negIndex hSecond := by
  unfold negIndex
  congr 1
  ext i
  simp [hPattern i]

/-- Positive inertia depends only on the positive eigenvalue sign pattern. -/
theorem posIndex_eq_of_same_positive_pattern
    {index : Type*} [Fintype index]
    {first second : Matrix index index ℂ}
    (hFirst : first.IsHermitian) (hSecond : second.IsHermitian)
    (hPattern : ∀ i,
      0 < hFirst.eigenvalues i ↔ 0 < hSecond.eigenvalues i) :
    posIndex hFirst = posIndex hSecond := by
  unfold posIndex
  congr 1
  ext i
  simp [hPattern i]

/-- Signed inertia is invariant under preservation of all eigenvalue signs. -/
theorem signedIndex_eq_of_same_sign_pattern
    {index : Type*} [Fintype index]
    {first second : Matrix index index ℂ}
    (hFirst : first.IsHermitian) (hSecond : second.IsHermitian)
    (hPattern : SameHermitianSignPattern hFirst hSecond) :
    (posIndex hFirst : ℤ) - (negIndex hFirst : ℤ) =
      (posIndex hSecond : ℤ) - (negIndex hSecond : ℤ) := by
  rw [posIndex_eq_of_same_positive_pattern hFirst hSecond hPattern.2,
    negIndex_eq_of_same_negative_pattern hFirst hSecond hPattern.1]

/-- Localizer signed index is invariant when the two localizer eigenvalue sign
patterns agree. -/
theorem finiteLocalizerSignedIndex_eq_of_same_sign_pattern
    (kappa₁ x₁ kappa₂ x₂ : ℝ)
    (X₁ H₁ X₂ H₂ : Matrix n n ℂ) (z₁ z₂ : ℂ)
    (hX₁ : X₁.IsHermitian) (hX₂ : X₂.IsHermitian)
    (hPattern : SameHermitianSignPattern
      (finiteHermitianLocalizer_isHermitian kappa₁ x₁ hX₁ H₁ z₁)
      (finiteHermitianLocalizer_isHermitian kappa₂ x₂ hX₂ H₂ z₂)) :
    finiteLocalizerSignedIndex kappa₁ x₁ X₁ H₁ z₁ hX₁ =
      finiteLocalizerSignedIndex kappa₂ x₂ X₂ H₂ z₂ hX₂ := by
  exact signedIndex_eq_of_same_sign_pattern _ _ hPattern

/-- A changed signed index rules out preservation of the full spectral sign
pattern. -/
theorem index_change_forces_sign_pattern_change
    (kappa₁ x₁ kappa₂ x₂ : ℝ)
    (X₁ H₁ X₂ H₂ : Matrix n n ℂ) (z₁ z₂ : ℂ)
    (hX₁ : X₁.IsHermitian) (hX₂ : X₂.IsHermitian)
    (hIndex :
      finiteLocalizerSignedIndex kappa₁ x₁ X₁ H₁ z₁ hX₁ ≠
        finiteLocalizerSignedIndex kappa₂ x₂ X₂ H₂ z₂ hX₂) :
    ¬ SameHermitianSignPattern
      (finiteHermitianLocalizer_isHermitian kappa₁ x₁ hX₁ H₁ z₁)
      (finiteHermitianLocalizer_isHermitian kappa₂ x₂ hX₂ H₂ z₂) := by
  intro hPattern
  exact hIndex
    (finiteLocalizerSignedIndex_eq_of_same_sign_pattern
      kappa₁ x₁ kappa₂ x₂ X₁ H₁ X₂ H₂ z₁ z₂ hX₁ hX₂ hPattern)

/-- Equality of all localizer data gives equality of the signed index. -/
theorem finiteLocalizerSignedIndex_refl
    (kappa x : ℝ) (X H : Matrix n n ℂ) (z : ℂ)
    (hX : X.IsHermitian) :
    finiteLocalizerSignedIndex kappa x X H z hX =
      finiteLocalizerSignedIndex kappa x X H z hX :=
  rfl

#print axioms negIndex_eq_of_same_negative_pattern
#print axioms posIndex_eq_of_same_positive_pattern
#print axioms signedIndex_eq_of_same_sign_pattern
#print axioms finiteLocalizerSignedIndex_eq_of_same_sign_pattern
#print axioms index_change_forces_sign_pattern_change

end

end D5.S3.SpectralTopology.FiniteLocalizerIndex
