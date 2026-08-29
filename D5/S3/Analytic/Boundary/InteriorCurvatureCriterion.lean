/- GID: D5/S3/Analytic/Boundary/InteriorCurvatureCriterion
   generality: I
   mirror-B: D5/B/S3/Analytic/Boundary/InteriorCurvatureCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Interior Riesz curvature vanishes exactly when every nontrivial zeta zero is critical. -/

import D5.S3.Weil.ZetaRvm.CountByIntegral
import Mathlib.MeasureTheory.Measure.Support

/- Library-search audit trail (2026-08-29):
   * Repository and pinned-Mathlib searches for an interior-curvature zero
     criterion found no exact theorem owner.
   * Frozen `IsNontrivialZero`, `zeroMult`, `one_le_mult_holds`, and
     `zeta_reflect_zero` supply the canonical zero carrier, its positive
     analytic multiplicity, and the reflection step for zeros left of the
     critical line.
   * Pinned Mathlib supplies `Measure.sum_eq_zero`, `Measure.smul_apply`, and
     `Measure.dirac_apply`. The missing bridge from vanishing of the atomic
     curvature measure to absence of right off-line zeros is proved locally;
     no new definition or alternate carrier is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Boundary.InteriorCurvatureCriterion

open Complex MeasureTheory Set
open scoped ENNReal

/-- The interior Riesz-curvature measure is constructed at the source points
`-im(rho) + I * (re(rho) - 1/2)`, with the source coefficient `2*pi*m_rho`.
It vanishes exactly when every canonical nontrivial zeta zero is critical. -/
theorem interior_curvature_criterion :
    let rightOffLineZeros : Set ℂ :=
      {rho | Zeta23.IsNontrivialZero rho ∧ (1 : ℝ) / 2 < rho.re}
    let upperPoint : rightOffLineZeros -> ℂ := fun rho =>
      (-rho.1.im : ℂ) + Complex.I *
        ((rho.1.re - (1 : ℝ) / 2 : ℝ) : ℂ)
    let interiorCurvature : Measure ℂ :=
      Measure.sum fun rho : rightOffLineZeros =>
        (ENNReal.ofReal (2 * Real.pi) *
          (Zeta23.zeroMult rho : ℝ≥0∞)) • Measure.dirac (upperPoint rho)
    (∀ rho : ℂ, Zeta23.IsNontrivialZero rho ->
      rho.re = (1 : ℝ) / 2) ↔ interiorCurvature = 0 := by
  classical
  dsimp only
  let rightOffLineZeros : Set ℂ :=
    {rho | Zeta23.IsNontrivialZero rho ∧ (1 : ℝ) / 2 < rho.re}
  let upperPoint : rightOffLineZeros -> ℂ := fun rho =>
    (-rho.1.im : ℂ) + Complex.I *
      ((rho.1.re - (1 : ℝ) / 2 : ℝ) : ℂ)
  change (∀ rho : ℂ, Zeta23.IsNontrivialZero rho ->
      rho.re = (1 : ℝ) / 2) ↔
    Measure.sum (fun rho : rightOffLineZeros =>
      (ENNReal.ofReal (2 * Real.pi) *
        (Zeta23.zeroMult rho : ℝ≥0∞)) • Measure.dirac (upperPoint rho)) = 0
  constructor
  · intro hCritical
    rw [Measure.sum_eq_zero]
    intro rho
    exfalso
    exact (ne_of_gt rho.property.2) (hCritical rho rho.property.1)
  · intro hCurvatureZero rho hRho
    have noRightZero (point : ℂ) (hPoint : Zeta23.IsNontrivialZero point)
        (hRight : (1 : ℝ) / 2 < point.re) : False := by
      let indexedPoint : rightOffLineZeros := ⟨point, hPoint, hRight⟩
      have hAtomZero :
          (ENNReal.ofReal (2 * Real.pi) *
            (Zeta23.zeroMult indexedPoint : ℝ≥0∞)) •
              Measure.dirac (upperPoint indexedPoint) = 0 :=
        (Measure.sum_eq_zero.mp hCurvatureZero) indexedPoint
      have hWeightPositive :
          0 < ENNReal.ofReal (2 * Real.pi) *
            (Zeta23.zeroMult indexedPoint : ℝ≥0∞) := by
        rw [ENNReal.mul_pos_iff]
        constructor
        · exact ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
        · exact_mod_cast Zeta23.ZetaSeam.one_le_mult_holds point hPoint
      have hAtUniv := congrArg
        (fun measure : Measure ℂ => measure Set.univ) hAtomZero
      simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_mem,
        Set.mem_univ, Pi.one_apply, smul_eq_mul, mul_one, Measure.coe_zero,
        Pi.zero_apply] at hAtUniv
      exact hWeightPositive.ne' hAtUniv
    by_cases hRight : (1 : ℝ) / 2 < rho.re
    · exact False.elim (noRightZero rho hRho hRight)
    by_cases hCritical : rho.re = (1 : ℝ) / 2
    · exact hCritical
    have hLeft : rho.re < (1 : ℝ) / 2 :=
      lt_of_le_of_ne (le_of_not_gt hRight) hCritical
    have hReflectedZero := Zeta23.zeta_reflect_zero rho hRho
    have hReflectedRight :
        (1 : ℝ) / 2 < (Zeta23.reflect rho).re := by
      simp only [Zeta23.reflect, Complex.sub_re, Complex.one_re,
        Complex.conj_re]
      linarith
    exact False.elim
      (noRightZero (Zeta23.reflect rho) hReflectedZero hReflectedRight)

#print axioms interior_curvature_criterion

end D5.S3.Analytic.Boundary.InteriorCurvatureCriterion
