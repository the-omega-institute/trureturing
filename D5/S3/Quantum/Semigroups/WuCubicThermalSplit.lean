import D5.S3.Quantum.Semigroups.WuCubicThermalBohrGap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.LeftRightNhds
import OmegaBuild.Commands

/-! The first-order cap splitting of the degree-one thermal coefficient. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology

namespace D5.S3.Quantum.Semigroups.WuCubicThermalSplit

open WuCubicThermalBohrGap
open D5.S3.Observer.Fluctuation.ThermalCoefficientFloor (coth)
open private hasDerivAt_mul_coth g_pos from
  D5.S3.Quantum.Semigroups.WuCubicThermalBohrGap

noncomputable section

/-- The degree-one coefficient at actual bias `v` and fixed cap `beta`. -/
def degreeOneCoefficient (beta v : ℝ) : ℝ :=
  (9 / 4) * Real.cosh (v / 6) * (1 - g v / g beta)

/-- The coefficient of the cap deficit `delta = beta - v` at the cap. -/
def capSplitSlope (beta : ℝ) : ℝ :=
  (9 / 4) * Real.cosh (beta / 6) * (deriv g beta / g beta)

private theorem hasDerivAt_g {beta : ℝ} (hbeta : 0 < beta) :
    HasDerivAt g
      (((Real.sinh (beta / 3) * Real.cosh (beta / 3) - beta / 3) /
          Real.sinh (beta / 3) ^ 2 +
        (Real.sinh (beta / 6) * Real.cosh (beta / 6) - beta / 6) /
          Real.sinh (beta / 6) ^ 2) / 18) beta := by
  have hthree : HasDerivAt (fun y : ℝ => (y / 3) * coth (y / 3))
      (((Real.sinh (beta / 3) * Real.cosh (beta / 3) - beta / 3) /
          Real.sinh (beta / 3) ^ 2) / 3) beta := by
    convert (hasDerivAt_mul_coth (x := beta / 3) (by positivity)).comp beta
      ((hasDerivAt_id beta).div_const 3) using 1 <;>
      (try funext y) <;> simp only [Function.comp_apply] <;> ring
  have hsix : HasDerivAt (fun y : ℝ => (y / 6) * coth (y / 6))
      (((Real.sinh (beta / 6) * Real.cosh (beta / 6) - beta / 6) /
          Real.sinh (beta / 6) ^ 2) / 6) beta := by
    convert (hasDerivAt_mul_coth (x := beta / 6) (by positivity)).comp beta
      ((hasDerivAt_id beta).div_const 6) using 1 <;>
      (try funext y) <;> simp only [Function.comp_apply] <;> ring
  have hsum :=
    ((hthree.const_mul (1 / 6 : ℝ)).add (hsix.const_mul (1 / 3 : ℝ)))
  have hsum' : HasDerivAt
      (fun y : ℝ => (1 / 6) * ((y / 3) * coth (y / 3)) +
        (1 / 3) * ((y / 6) * coth (y / 6)))
      (((Real.sinh (beta / 3) * Real.cosh (beta / 3) - beta / 3) /
          Real.sinh (beta / 3) ^ 2 +
        (Real.sinh (beta / 6) * Real.cosh (beta / 6) - beta / 6) /
          Real.sinh (beta / 6) ^ 2) / 18) beta := by
    convert hsum using 1 <;> (try funext y) <;> ring
  apply hsum'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hbeta] with y hy
  rw [g, ite_eq_right hy.ne']
  ring

private theorem deriv_g_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < deriv g beta := by
  have hthree : 0 <
      (Real.sinh (beta / 3) * Real.cosh (beta / 3) - beta / 3) /
        Real.sinh (beta / 3) ^ 2 := by
    have hs := Real.self_lt_sinh_iff.mpr (show 0 < 2 * (beta / 3) by positivity)
    rw [Real.sinh_two_mul] at hs
    exact div_pos (by nlinarith only [hs])
      (sq_pos_of_pos (Real.sinh_pos_iff.mpr (by positivity)))
  have hsix : 0 <
      (Real.sinh (beta / 6) * Real.cosh (beta / 6) - beta / 6) /
        Real.sinh (beta / 6) ^ 2 := by
    have hs := Real.self_lt_sinh_iff.mpr (show 0 < 2 * (beta / 6) by positivity)
    rw [Real.sinh_two_mul] at hs
    exact div_pos (by nlinarith only [hs])
      (sq_pos_of_pos (Real.sinh_pos_iff.mpr (by positivity)))
  rw [(hasDerivAt_g hbeta).deriv]
  nlinarith

/-- The fixed-cap slope is strictly positive at every positive cap. -/
theorem capSplitSlope_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < capSplitSlope beta := by
  unfold capSplitSlope
  exact mul_pos (mul_pos (by norm_num) (Real.cosh_pos _))
    (div_pos (deriv_g_pos hbeta) (g_pos hbeta.le))

theorem degreeOneCoefficient_at_cap {beta : ℝ} (hbeta : 0 < beta) :
    degreeOneCoefficient beta beta = 0 := by
  unfold degreeOneCoefficient
  rw [div_self (g_pos hbeta.le).ne']
  ring

/-- At the cap, the delta-parametrized coefficient has the exact positive slope. -/
theorem degreeOneCoefficient_hasDerivAt_cap {beta : ℝ} (hbeta : 0 < beta) :
    HasDerivAt (fun delta : ℝ => degreeOneCoefficient beta (beta - delta))
      (capSplitSlope beta) 0 := by
  have hratio : HasDerivAt (fun v : ℝ => g v / g beta)
      (deriv g beta / g beta) beta := by
    have h := (hasDerivAt_g hbeta).div (hasDerivAt_const beta (g beta))
      (g_pos hbeta.le).ne'
    refine h.congr_deriv ?_
    field_simp [(g_pos hbeta.le).ne'] <;> ring
  have hcosh : HasDerivAt (fun v : ℝ => Real.cosh (v / 6))
      (Real.sinh (beta / 6) / 6) beta := by
    convert (Real.hasDerivAt_cosh (beta / 6)).comp beta
      ((hasDerivAt_id beta).div_const 6) using 1 <;>
      (try funext y) <;> simp only [Function.comp_apply] <;> ring
  have hcoeff : HasDerivAt (fun v : ℝ => degreeOneCoefficient beta v)
      (-capSplitSlope beta) beta := by
    have h := ((hcosh.const_mul (9 / 4 : ℝ)).mul
      ((hasDerivAt_const beta (1 : ℝ)).sub hratio))
    refine h.congr_deriv ?_
    unfold degreeOneCoefficient capSplitSlope
    rw [div_self (g_pos hbeta.le).ne']
    ring
  have hshift := hcoeff.comp_of_eq 0
    ((hasDerivAt_const (0 : ℝ) beta).sub (hasDerivAt_id (0 : ℝ)))
    (by simp)
  simpa [Function.comp_def] using hshift.congr_deriv (by ring)

/-- The positive cap split is uniformly linear on a sufficiently small
nonnegative delta interval, with explicit one-half and three-halves factors. -/
theorem degreeOneCoefficient_linear_bounds {beta : ℝ} (hbeta : 0 < beta) :
    ∃ epsilon > 0, ∀ delta : ℝ, 0 ≤ delta → delta ≤ epsilon →
      capSplitSlope beta / 2 * delta ≤ degreeOneCoefficient beta (beta - delta) ∧
      degreeOneCoefficient beta (beta - delta) ≤ 3 / 2 * capSplitSlope beta * delta := by
  let F : ℝ → ℝ := fun delta => degreeOneCoefficient beta (beta - delta)
  have hF : HasDerivAt F (capSplitSlope beta) 0 := by
    simpa [F] using degreeOneCoefficient_hasDerivAt_cap hbeta
  have hslope := hF.tendsto_slope_zero_right
  have hhalf : capSplitSlope beta / 2 < capSplitSlope beta := by
    linarith [capSplitSlope_pos hbeta]
  have hthree : capSplitSlope beta < 3 / 2 * capSplitSlope beta := by
    linarith [capSplitSlope_pos hbeta]
  have hquot : ∀ᶠ delta : ℝ in 𝓝[>] 0,
      capSplitSlope beta / 2 <
          delta⁻¹ • (F (0 + delta) - F 0) ∧
        delta⁻¹ • (F (0 + delta) - F 0) < 3 / 2 * capSplitSlope beta := by
    have hlo := hslope.eventually (eventually_gt_nhds hhalf)
    have hhi := hslope.eventually (eventually_lt_nhds hthree)
    filter_upwards [hlo, hhi] with delta hdelta_lo hdelta_hi
    exact ⟨hdelta_lo, hdelta_hi⟩
  have hquot_mem :
      {delta : ℝ |
        capSplitSlope beta / 2 < delta⁻¹ • (F (0 + delta) - F 0) ∧
          delta⁻¹ • (F (0 + delta) - F 0) < 3 / 2 * capSplitSlope beta} ∈
      𝓝[>] 0 := hquot
  obtain ⟨epsilon₀, hepsilon₀, hquot₀⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0 : ℝ) < 1 by norm_num)).mp hquot_mem
  let epsilon := min (epsilon₀ / 2) beta
  have hepsilon : 0 < epsilon := lt_min (by linarith) hbeta
  refine ⟨epsilon, hepsilon, ?_⟩
  intro delta hdelta hdeltaε
  by_cases hdelta_zero : delta = 0
  · subst delta
    simpa [F, degreeOneCoefficient_at_cap hbeta]
  have hdelta_pos : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hdelta_zero)
  have hdelta_half : delta ≤ epsilon₀ / 2 :=
    hdeltaε.trans (min_le_left _ _)
  have hdelta_lt : delta < epsilon₀ := by linarith
  have hsec := hquot₀ ⟨hdelta_pos, hdelta_lt⟩
  have hsec_lo := hsec.1
  have hsec_hi := hsec.2
  simp only [smul_eq_mul, zero_add] at hsec_lo hsec_hi
  have hFzero : F 0 = 0 := by
    simpa [F] using degreeOneCoefficient_at_cap hbeta
  simp only [hFzero, sub_zero] at hsec_lo hsec_hi
  have hlo := mul_lt_mul_of_pos_left hsec_lo hdelta_pos
  have hhi := mul_lt_mul_of_pos_left hsec_hi hdelta_pos
  have hcancel : delta * (delta⁻¹ * F delta) = F delta := by
    rw [← mul_assoc, mul_inv_cancel₀ hdelta_zero, one_mul]
  constructor
  · calc
      capSplitSlope beta / 2 * delta = delta * (capSplitSlope beta / 2) := by ring
      _ ≤ delta * (delta⁻¹ * F delta) := hlo.le
      _ = F delta := hcancel
      _ = degreeOneCoefficient beta (beta - delta) := rfl
  · calc
      degreeOneCoefficient beta (beta - delta) = F delta := rfl
      _ = delta * (delta⁻¹ * F delta) := hcancel.symm
      _ ≤ delta * (3 / 2 * capSplitSlope beta) := hhi.le
      _ = 3 / 2 * capSplitSlope beta * delta := by ring

#print axioms capSplitSlope_pos
#print axioms degreeOneCoefficient_hasDerivAt_cap
#print axioms degreeOneCoefficient_linear_bounds

end
end D5.S3.Quantum.Semigroups.WuCubicThermalSplit
