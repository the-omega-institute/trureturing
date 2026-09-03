/- GID: D5/S3/Observer/GoldenShadowOperator
   generality: G
   mirror-B: D5/B/S3/Observer/GoldenShadowOperator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive operator satisfying the golden shadow identity is scalar on its active space. -/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * Repository searches covered golden-shadow terminology, positive
     contractions, active subspaces, Gram operators, spectra, singular values,
     formalization receipts, digest indexes, generalized polynomial spectral
     collapse results, and in-flight math lanes. No equivalent theorem exists.
   * `GoldenTwoShadowBound` proves sharp polynomial inequalities, but not the
     equality-case scalar or spectral collapse proved here.
   * Pinned Mathlib supplies `eqOn_of_cfc_eq_cfc`,
     `CFC.eq_algebraMap_of_spectrum_subset_singleton`,
     `spectrum_nonneg_of_nonneg`, `CFC.spectrum_algebraMap_eq`,
     `norm_algebraMap'`, and the golden-ratio identities used below. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenShadowOperator

open scoped CStarAlgebra

/-- On a nonzero active Hilbert space, a positive operator satisfying
`I = D + D^2` is exactly the inverse-golden scalar operator. Its complementary
shadow equals its square, both are the inverse-golden-square scalar operator,
and its spectrum and norm collapse to the inverse golden ratio.

The source's contraction assumption is unnecessary: the displayed identity
and positivity already determine the operator and hence its norm. The
nontriviality assumption is necessary for the asserted singleton spectrum and
positive norm; on the zero space the spectrum is empty and every norm is zero. -/
theorem golden_shadow_operator_theorem
    (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [Nontrivial E]
    (D : E →L[ℂ] E) (hD : 0 ≤ D) (hGolden : 1 = D + D ^ 2) :
    D = algebraMap ℝ (E →L[ℂ] E) Real.goldenRatio⁻¹ ∧
      1 - D = algebraMap ℝ (E →L[ℂ] E) (Real.goldenRatio⁻¹ ^ 2) ∧
      D ^ 2 = algebraMap ℝ (E →L[ℂ] E) (Real.goldenRatio⁻¹ ^ 2) ∧
      spectrum ℝ D = {Real.goldenRatio⁻¹} ∧
      ‖D‖ = Real.goldenRatio⁻¹ := by
  let r : ℝ := Real.goldenRatio⁻¹
  have hrPos : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hrEq : r = Real.goldenRatio - 1 := by
    dsimp only [r]
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hrSplit : r + r ^ 2 = 1 := by
    rw [hrEq]
    nlinarith [Real.goldenRatio_sq]
  have hSelf : IsSelfAdjoint D := IsSelfAdjoint.of_nonneg hD
  have hPolyCfc :
      cfc (fun x : ℝ => x + x ^ 2) D = D + D ^ 2 := by
    change cfc (fun x : ℝ => id x + (id x) ^ 2) D = D + D ^ 2
    rw [cfc_add D id (fun x : ℝ => (id x) ^ 2), cfc_id ℝ D,
      cfc_pow id 2 D, cfc_id ℝ D]
  have hOneCfc : cfc (fun _ : ℝ => 1) D = 1 := by
    rw [cfc_const (1 : ℝ) D, map_one]
  have hPointwise :
      (spectrum ℝ D).EqOn (fun x : ℝ => x + x ^ 2) (fun _ => 1) := by
    apply eqOn_of_cfc_eq_cfc (ha := hSelf)
    calc
      cfc (fun x : ℝ => x + x ^ 2) D = D + D ^ 2 := hPolyCfc
      _ = 1 := hGolden.symm
      _ = cfc (fun _ : ℝ => 1) D := hOneCfc.symm
  have hSpectrumSubset : spectrum ℝ D ⊆ {r} := by
    intro x hx
    have hxNonnegative : 0 ≤ x := spectrum_nonneg_of_nonneg hD hx
    have hxEquation : x + x ^ 2 = 1 := hPointwise hx
    have hFactor : (x - r) * (x + r + 1) = 0 := by
      nlinarith [hrSplit]
    have hSecondPositive : 0 < x + r + 1 := by linarith
    have hxEq : x = r := by
      rcases mul_eq_zero.mp hFactor with hFirst | hSecond
      · linarith
      · exact (ne_of_gt hSecondPositive hSecond).elim
    simpa [hxEq]
  have hScalar : D = algebraMap ℝ (E →L[ℂ] E) r :=
    CFC.eq_algebraMap_of_spectrum_subset_singleton D r hSpectrumSubset hSelf
  have hComplement :
      1 - D = algebraMap ℝ (E →L[ℂ] E) (r ^ 2) := by
    rw [hScalar, ← map_one (algebraMap ℝ (E →L[ℂ] E)), ← map_sub]
    congr 1
    linarith [hrSplit]
  have hSquare :
      D ^ 2 = algebraMap ℝ (E →L[ℂ] E) (r ^ 2) := by
    calc
      D ^ 2 = 1 - D := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact hGolden.symm
      _ = algebraMap ℝ (E →L[ℂ] E) (r ^ 2) := hComplement
  have hSpectrum : spectrum ℝ D = {r} := by
    rw [hScalar, CFC.spectrum_algebraMap_eq]
  have hNorm : ‖D‖ = r := by
    rw [hScalar, norm_algebraMap', Real.norm_eq_abs, abs_of_pos hrPos]
  exact ⟨hScalar, hComplement, hSquare, hSpectrum, hNorm⟩

end D5.S3.Observer.GoldenShadowOperator
