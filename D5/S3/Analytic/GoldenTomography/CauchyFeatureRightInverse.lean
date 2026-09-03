/- GID: D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct support coordinates away from one center give an explicitly invertible finite Cauchy-jet feature matrix. -/

import D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Cauchy-feature right inverse through one jet center

At one complex center, the successive Cauchy jet coordinates of a support
point are reciprocal powers of its affine distance from the center. The
resulting square feature matrix factors as a nonzero diagonal matrix times a
Vandermonde matrix in the reciprocal nodes. Distinct supports therefore give
an explicit two-sided inverse whenever the center avoids every support.

This node proves a certified sampling scheme for Cauchy jets. It does not yet
assert full rank for an arbitrary matrix of independently chosen Cauchy sample
points `1 / (support a - point j)`.
-/

/- Library-search audit trail (2026-09-03):
   * `FiniteVandermondeTomography.vandermonde_det_ne_zero_of_injective`
     already owns the distinct-node determinant argument and is reused here.
   * Pinned Mathlib supplies injectivity of inversion, diagonal and product
     determinant formulas, the nonsingular matrix inverse, and
     `Matrix.mulVec_injective_iff_isUnit`.
   * Repository searches for `CauchyFeatureRightInverse`, Cauchy-jet feature
     inverses, and a reciprocal-node Vandermonde factorization found no public
     owner.
   * The finite atomic Stieltjes branch uses first Cauchy features. This module
     stays independent of that open branch and supplies the reusable jet-level
     right-inverse theorem needed by a later adapter. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Finset

namespace D5.S3.Analytic.GoldenTomography.CauchyFeatureRightInverse

open D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography

/-- The reciprocal affine distance from a support coordinate to one center. -/
def reciprocalCauchyNode {n : ℕ}
    (support : Fin n → ℂ) (center : ℂ) : Fin n → ℂ :=
  fun a => (support a - center)⁻¹

/-- The square Cauchy-jet feature matrix. Row `a` contains the reciprocal
powers of `support a - center`, beginning with power one. -/
def cauchyJetFeatureMatrix {n : ℕ}
    (support : Fin n → ℂ) (center : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (reciprocalCauchyNode support center) *
    Matrix.vandermonde (reciprocalCauchyNode support center)

/-- The canonical candidate right inverse is the nonsingular matrix inverse. -/
def cauchyJetFeatureRightInverse {n : ℕ}
    (support : Fin n → ℂ) (center : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (cauchyJetFeatureMatrix support center)⁻¹

/-- Distinct supports remain distinct after subtracting a common center and
applying inversion. -/
theorem reciprocal_cauchy_nodes_injective {n : ℕ}
    {support : Fin n → ℂ} {center : ℂ}
    (hSupport : Function.Injective support) :
    Function.Injective (reciprocalCauchyNode support center) := by
  intro a b hEqual
  apply hSupport
  have hSub : support a - center = support b - center :=
    inv_injective hEqual
  exact sub_right_injective hSub

/-- Avoiding the center makes every reciprocal node nonzero. -/
theorem reciprocal_cauchy_node_ne_zero {n : ℕ}
    (support : Fin n → ℂ) (center : ℂ)
    (hCenter : ∀ a, support a ≠ center) (a : Fin n) :
    reciprocalCauchyNode support center a ≠ 0 := by
  exact inv_ne_zero (sub_ne_zero.mpr (hCenter a))

/-- The Cauchy-jet matrix entry is the corresponding reciprocal power. -/
theorem cauchy_jet_feature_matrix_apply {n : ℕ}
    (support : Fin n → ℂ) (center : ℂ) (a k : Fin n) :
    cauchyJetFeatureMatrix support center a k =
      (support a - center)⁻¹ ^ ((k : ℕ) + 1) := by
  simp [cauchyJetFeatureMatrix, reciprocalCauchyNode,
    Matrix.mul_apply, Matrix.vandermonde]
  ring

/-- Distinct supports away from the center make the Cauchy-jet feature matrix
nonsingular. -/
theorem cauchy_jet_feature_det_ne_zero {n : ℕ}
    {support : Fin n → ℂ} {center : ℂ}
    (hSupport : Function.Injective support)
    (hCenter : ∀ a, support a ≠ center) :
    Matrix.det (cauchyJetFeatureMatrix support center) ≠ 0 := by
  unfold cauchyJetFeatureMatrix
  rw [Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun a _ =>
      reciprocal_cauchy_node_ne_zero support center hCenter a
  · exact vandermonde_det_ne_zero_of_injective
      (reciprocal_cauchy_nodes_injective hSupport)

/-- Multiplying by the canonical right inverse gives the identity. -/
theorem cauchy_jet_feature_mul_rightInverse {n : ℕ}
    {support : Fin n → ℂ} {center : ℂ}
    (hSupport : Function.Injective support)
    (hCenter : ∀ a, support a ≠ center) :
    cauchyJetFeatureMatrix support center *
        cauchyJetFeatureRightInverse support center = 1 := by
  unfold cauchyJetFeatureRightInverse
  exact Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr
      (cauchy_jet_feature_det_ne_zero hSupport hCenter))

/-- The same inverse is also a left inverse. -/
theorem cauchy_jet_feature_rightInverse_mul {n : ℕ}
    {support : Fin n → ℂ} {center : ℂ}
    (hSupport : Function.Injective support)
    (hCenter : ∀ a, support a ≠ center) :
    cauchyJetFeatureRightInverse support center *
        cauchyJetFeatureMatrix support center = 1 := by
  unfold cauchyJetFeatureRightInverse
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr
      (cauchy_jet_feature_det_ne_zero hSupport hCenter))

/-- Cauchy-jet analysis is injective under the same explicit hypotheses. -/
theorem cauchy_jet_feature_mulVec_injective {n : ℕ}
    {support : Fin n → ℂ} {center : ℂ}
    (hSupport : Function.Injective support)
    (hCenter : ∀ a, support a ≠ center) :
    Function.Injective (cauchyJetFeatureMatrix support center).mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr
    (cauchy_jet_feature_det_ne_zero hSupport hCenter)

/-- The two-sided inverse and injective analysis map are packaged as one
finite Cauchy-feature certificate. -/
theorem cauchy_feature_right_inverse {n : ℕ}
    {support : Fin n → ℂ} {center : ℂ}
    (hSupport : Function.Injective support)
    (hCenter : ∀ a, support a ≠ center) :
    cauchyJetFeatureMatrix support center *
        cauchyJetFeatureRightInverse support center = 1 ∧
      cauchyJetFeatureRightInverse support center *
        cauchyJetFeatureMatrix support center = 1 ∧
      Function.Injective (cauchyJetFeatureMatrix support center).mulVec := by
  exact ⟨
    cauchy_jet_feature_mul_rightInverse hSupport hCenter,
    cauchy_jet_feature_rightInverse_mul hSupport hCenter,
    cauchy_jet_feature_mulVec_injective hSupport hCenter⟩

#print axioms reciprocal_cauchy_nodes_injective
#print axioms cauchy_jet_feature_matrix_apply
#print axioms cauchy_jet_feature_det_ne_zero
#print axioms cauchy_jet_feature_mul_rightInverse
#print axioms cauchy_jet_feature_rightInverse_mul
#print axioms cauchy_jet_feature_mulVec_injective
#print axioms cauchy_feature_right_inverse

end D5.S3.Analytic.GoldenTomography.CauchyFeatureRightInverse
