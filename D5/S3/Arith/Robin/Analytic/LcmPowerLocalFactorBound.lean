/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Bernoulli lower bound for the normalized local LCM power factor. -/

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace D5.S3.Arith.Robin.Analytic.LcmPowerLocalFactorBound

/-- The normalized local factor appearing after dividing a prime-power term by its
geometric scale. -/
def normalizedLocalFactor (κ r a : ℝ) : ℝ :=
  (1 - r) ^ (-κ) * ((1 - r ^ (a + 1)) ^ κ - r ^ κ * (1 - r ^ a) ^ κ)

/-- The uniform coefficient used in the local-factor lower bound. -/
def localFactorConstant (κ : ℝ) : ℝ := κ / (1 - (1 / 2 : ℝ) ^ κ)

private lemma bernoulli_rpow {κ u : ℝ} (hκ : 1 ≤ κ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 - κ * u ≤ (1 - u) ^ κ := by
  rcases eq_or_lt_of_le hu0 with rfl | hu
  · simp
  have hconv := convexOn_rpow hκ
  have hxmem : 1 - u ∈ Ici (0 : ℝ) := sub_nonneg.mpr hu1
  have hymem : (1 : ℝ) ∈ Ici (0 : ℝ) := by simp
  have hxy : 1 - u < (1 : ℝ) := by linarith
  have hderiv : HasDerivAt (fun x : ℝ => x ^ κ) κ 1 := by
    convert (hasDerivAt_id (1 : ℝ)).rpow_const (p := κ) (Or.inl (by norm_num)) using 1 <;> norm_num
  have hs := hconv.slope_le_of_hasDerivAt hxmem hymem hxy hderiv
  rw [slope_def_field] at hs
  have hs' : (1 - (1 - u) ^ κ) / u ≤ κ := by
    simpa only [Real.one_rpow, sub_sub_cancel] using hs
  have hmul := (div_le_iff₀ hu).mp hs'
  linarith

/-- The local-factor lower bound from the Bernoulli estimate.

The expression on the left is the exact normalized difference
`(1-r)^(-κ) ((1-r^(a+1))^κ-r^κ(1-r^a)^κ)`. -/
theorem local_factor_lower_bound {κ r a : ℝ} (hκ : 1 ≤ κ) (hr0 : 0 ≤ r)
    (hrhalf : r ≤ 1 / 2) (ha : 1 ≤ a) :
    normalizedLocalFactor κ r a ≥
      (1 - r) ^ (-κ) * (1 - r ^ κ) *
        (1 - localFactorConstant κ * r ^ (a + 1)) := by
  have hr1 : r ≤ 1 := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hu0 : 0 ≤ r ^ (a + 1) := Real.rpow_nonneg hr0 _
  have hua : 0 ≤ a + 1 := by linarith
  have hu1 : r ^ (a + 1) ≤ 1 := Real.rpow_le_one hr0 hr1 hua
  have hra0 : 0 ≤ r ^ a := Real.rpow_nonneg hr0 _
  have hra1 : r ^ a ≤ 1 := Real.rpow_le_one hr0 hr1 (by linarith)
  have hbase0 : 0 ≤ 1 - r ^ a := sub_nonneg.mpr hra1
  have hpow_le : (1 - r ^ a) ^ κ ≤ 1 := by
    exact Real.rpow_le_one hbase0 (by linarith) hκ0
  have hrκ0 : 0 ≤ r ^ κ := Real.rpow_nonneg hr0 _
  have hterm_le : r ^ κ * (1 - r ^ a) ^ κ ≤ r ^ κ := by
    exact mul_le_of_le_one_right hrκ0 hpow_le
  have hbern := bernoulli_rpow hκ hu0 hu1
  have hcore : 1 - κ * r ^ (a + 1) - r ^ κ ≤
      (1 - r ^ (a + 1)) ^ κ - r ^ κ * (1 - r ^ a) ^ κ := by
    linarith
  have hhalfκ : (1 / 2 : ℝ) ^ κ < 1 := by
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hdenpos : 0 < 1 - (1 / 2 : ℝ) ^ κ := sub_pos.mpr hhalfκ
  have hrκ_le : r ^ κ ≤ (1 / 2 : ℝ) ^ κ := by
    exact Real.rpow_le_rpow hr0 hrhalf hκ0
  have hcoeff : κ ≤ localFactorConstant κ * (1 - r ^ κ) := by
    dsimp [localFactorConstant]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hdenpos).2
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hrκ_le 1) (by positivity)
  have hfactor : (1 - r ^ κ) *
      (1 - localFactorConstant κ * r ^ (a + 1)) ≤
      1 - κ * r ^ (a + 1) - r ^ κ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrκ_le) hu0]
  have hcombined : (1 - r ^ κ) *
      (1 - localFactorConstant κ * r ^ (a + 1)) ≤
      (1 - r ^ (a + 1)) ^ κ - r ^ κ * (1 - r ^ a) ^ κ :=
    hfactor.trans hcore
  have hscale0 : 0 ≤ (1 - r) ^ (-κ) := Real.rpow_nonneg (by linarith) _
  dsimp [normalizedLocalFactor]
  simpa only [ge_iff_le, mul_assoc] using
    (mul_le_mul_of_nonneg_left hcombined hscale0)

end D5.S3.Arith.Robin.Analytic.LcmPowerLocalFactorBound
