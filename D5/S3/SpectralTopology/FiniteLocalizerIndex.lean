/- GID: D5/S3/SpectralTopology/FiniteLocalizerIndex
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/FiniteLocalizerIndex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Hermitian localizers carry proof-independent positive and negative inertia counts with explicit dimension bounds. -/

import D5.S3.SpectralTopology.FinitePointGapLocalizer
import Mathlib.Tactic

/-!
# Finite localizer inertia index

A Hermitian finite spectral localizer has positive and negative inertia counts.
Their integer difference is the finite localizer signature. This module proves
that the counts are independent of the proof of Hermitianity, are bounded by
the doubled matrix dimension, and remain defined on every point-gap
certificate supplied by the zero-scale localizer bridge.

These are finite inertia data. Local constancy under norm-small perturbations,
homotopy invariance, half-signature normalization, K-theory identification,
and infinite-volume stability remain separate theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.SpectralTopology.FiniteLocalizerIndex

open D5.S3.SpectralTopology.FiniteHermitianLocalizer
open D5.S3.SpectralTopology.FinitePointGapLocalizer

noncomputable section

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Positive inertia of a finite Hermitian localizer. -/
def localizerPositiveIndex
    {X H : Matrix n n ℂ} (hX : X.IsHermitian)
    (x : ℝ) (z : ℂ) (kappa : ℝ) : ℕ :=
  RHLinalg.posIndex
    (finiteHermitianLocalizer_isHermitian hX x z kappa)

/-- Integer signature of the finite Hermitian localizer. -/
def finiteLocalizerSignature
    {X H : Matrix n n ℂ} (hX : X.IsHermitian)
    (x : ℝ) (z : ℂ) (kappa : ℝ) : ℤ :=
  (localizerPositiveIndex hX x z kappa : ℤ) -
    (localizerNegativeIndex hX x z kappa : ℤ)

/-- A packaged finite localizer inertia profile. -/
structure FiniteLocalizerInertia where
  positive : ℕ
  negative : ℕ
  signature : ℤ
  signature_eq : signature = (positive : ℤ) - (negative : ℤ)

/-- Inertia profile associated with one finite localizer. -/
def finiteLocalizerInertia
    {X H : Matrix n n ℂ} (hX : X.IsHermitian)
    (x : ℝ) (z : ℂ) (kappa : ℝ) : FiniteLocalizerInertia where
  positive := localizerPositiveIndex hX x z kappa
  negative := localizerNegativeIndex hX x z kappa
  signature := finiteLocalizerSignature hX x z kappa
  signature_eq := rfl

/-- The positive count is independent of the chosen Hermitianity proof for
`X`. -/
theorem localizerPositiveIndex_proof_irrel
    {X H : Matrix n n ℂ} (hX hX' : X.IsHermitian)
    (x : ℝ) (z : ℂ) (kappa : ℝ) :
    localizerPositiveIndex hX x z kappa =
      localizerPositiveIndex hX' x z kappa := by
  congr

/-- The negative count is independent of the chosen Hermitianity proof for
`X`. -/
theorem localizerNegativeIndex_proof_irrel
    {X H : Matrix n n ℂ} (hX hX' : X.IsHermitian)
    (x : ℝ) (z : ℂ) (kappa : ℝ) :
    localizerNegativeIndex hX x z kappa =
      localizerNegativeIndex hX' x z kappa := by
  congr

/-- Positive inertia cannot exceed the doubled finite dimension. -/
theorem localizerPositiveIndex_le_dimension
    {X H : Matrix n n ℂ} (hX : X.IsHermitian)
    (x : ℝ) (z : ℂ) (kappa : ℝ) :
    localizerPositiveIndex hX x z kappa ≤ 2 * Fintype.card n := by
  unfold localizerPositiveIndex RHLinalg.posIndex
  calc
    Finset.card
        {i | 0 <
          (finiteHermitianLocalizer_isHermitian hX x z kappa).eigenvalues i} ≤
        Fintype.card (n ⊕ n) := by
      simpa using Finset.card_le_card
        (Finset.filter_subset
          (fun i : n ⊕ n =>
            0 < (finiteHermitianLocalizer_isHermitian hX x z kappa).eigenvalues i)
          Finset.univ)
    _ = 2 * Fintype.card n := by
      simp [two_mul]

/-- Negative inertia cannot exceed the doubled finite dimension. -/
theorem localizerNegativeIndex_le_dimension
    {X H : Matrix n n ℂ} (hX : X.IsHermitian)
    (x : ℝ) (z : ℂ) (kappa : ℝ) :
    localizerNegativeIndex hX x z kappa ≤ 2 * Fintype.card n := by
  unfold localizerNegativeIndex RHLinalg.negIndex
  calc
    Finset.card
        {i | (finiteHermitianLocalizer_isHermitian hX x z kappa).eigenvalues i < 0} ≤
        Fintype.card (n ⊕ n) := by
      simpa using Finset.card_le_card
        (Finset.filter_subset
          (fun i : n ⊕ n =>
            (finiteHermitianLocalizer_isHermitian hX x z kappa).eigenvalues i < 0)
          Finset.univ)
    _ = 2 * Fintype.card n := by
      simp [two_mul]

/-- The packaged profile records the same integer signature as the direct
definition. -/
theorem finiteLocalizerInertia_signature
    {X H : Matrix n n ℂ} (hX : X.IsHermitian)
    (x : ℝ) (z : ℂ) (kappa : ℝ) :
    (finiteLocalizerInertia hX x z kappa).signature =
      finiteLocalizerSignature hX x z kappa := by
  rfl

/-- A point-gap certificate places the zero-scale localizer in the invertible
Hermitian locus on which its inertia profile can be evaluated. -/
theorem pointGap_has_invertible_localizer_inertia
    {X H : Matrix n n ℂ} (hX : X.IsHermitian)
    (x : ℝ) (z : ℂ) (hGap : HasPointGap H z) :
    IsUnit (finiteHermitianLocalizer X H x z 0) ∧
      (finiteLocalizerInertia hX x z 0).positive ≤
        2 * Fintype.card n ∧
      (finiteLocalizerInertia hX x z 0).negative ≤
        2 * Fintype.card n := by
  exact ⟨zeroScaleLocalizer_isUnit_of_hasPointGap X x hGap,
    localizerPositiveIndex_le_dimension hX x z 0,
    localizerNegativeIndex_le_dimension hX x z 0⟩

example : FiniteLocalizerInertia :=
  finiteLocalizerInertia
    (X := (0 : Matrix (Fin 1) (Fin 1) ℂ))
    (H := 0) (by simp) 0 0 0

#print axioms localizerPositiveIndex_proof_irrel
#print axioms localizerNegativeIndex_proof_irrel
#print axioms localizerPositiveIndex_le_dimension
#print axioms localizerNegativeIndex_le_dimension
#print axioms pointGap_has_invertible_localizer_inertia

end

end D5.S3.SpectralTopology.FiniteLocalizerIndex
