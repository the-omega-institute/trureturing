/- GID: D5/S3/Divergence/MeanKernels/MeanKernelLowerTower
   generality: G
   mirror-B: D5/B/S3/Divergence/MeanKernels/MeanKernelLowerTower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For positive reals a ≠ b with a + b ≤ 2, the reciprocal kernels of the logarithmic, geometric and harmonic means satisfy (log a − log b)/(a−b) ≤ 1/√(ab) ≤ (a⁻¹+b⁻¹)/2 ≤ 1/(ab). Reciprocating, this is the mean chain HM ≤ GM ≤ L together with the density endpoint GM² ≤ HM ⟺ a + b ≤ 2. It is the lower portion of the reciprocal-mean tower; the top link 2/(a+b) ≤ (log a − log b)/(a−b) (the L ≤ A step) is recorded separately in the sibling logarithmic-mean sandwich, and the operator divergence tower this scalar chain drives is not covered here. The geometric–logarithmic step GM ≤ L is proved from x ≤ sinh x at x = log √(a/b). -/

import Mathlib

open Real

namespace D5.S3.Divergence.MeanKernels.MeanKernelLowerTower

/-- Ordered lower reciprocal-mean tower for `b < a`, both positive, with `a + b ≤ 2`: the reciprocal
logarithmic-mean kernel is bounded above by the reciprocal geometric, harmonic and squared-geometric
kernels in turn. -/
private theorem tower_ordered {a b : ℝ} (hb : 0 < b) (hab : b < a) (hsum : a + b ≤ 2) :
    (Real.log a - Real.log b) / (a - b) ≤ 1 / Real.sqrt (a * b)
    ∧ 1 / Real.sqrt (a * b) ≤ (a⁻¹ + b⁻¹) / 2
    ∧ (a⁻¹ + b⁻¹) / 2 ≤ 1 / (a * b) := by
  have ha : 0 < a := lt_trans hb hab
  have hab_pos : 0 < a - b := sub_pos.mpr hab
  have hba : 0 < a / b := div_pos ha hb
  have hgpos : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr (by positivity)
  have hg2 : (Real.sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (by positivity)
  have hAMGM : 2 * Real.sqrt (a * b) ≤ a + b := by
    nlinarith [hg2, sq_nonneg (a - b), hgpos, ha, hb]
  set u := Real.sqrt (a / b) with hu_def
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = a / b := Real.sq_sqrt (le_of_lt hba)
  have hu2ge1 : 1 ≤ u ^ 2 := by rw [hu2]; exact (one_le_div hb).mpr (le_of_lt hab)
  have hu1 : 1 ≤ u := by nlinarith [hu2ge1, hu0]
  have hupos : 0 < u := lt_of_lt_of_le one_pos hu1
  have ha_eq : a = b * u ^ 2 := by rw [hu2]; field_simp
  have hg_eq : Real.sqrt (a * b) = b * u := by
    have hsq : a * b = (b * u) ^ 2 := by rw [ha_eq]; ring
    rw [hsq, Real.sqrt_sq (by positivity)]
  refine ⟨?_, ?_, ?_⟩
  · -- GM ≤ L : (log a − log b)/(a−b) ≤ 1/√(ab), via x ≤ sinh x at x = log u
    have hlog : Real.log a - Real.log b = 2 * Real.log u := by
      rw [← Real.log_div (ne_of_gt ha) (ne_of_gt hb), ← hu2, Real.log_pow]; push_cast; ring
    have hu' : u ≠ 0 := ne_of_gt hupos
    have hkey : u * (1 / u) = 1 := by rw [mul_one_div, div_self hu']
    have hstep : 2 * u * Real.log u ≤ u ^ 2 - 1 := by
      have hlogle : Real.log u ≤ (u - 1 / u) / 2 := by
        have key : Real.log u ≤ Real.sinh (Real.log u) :=
          (Real.self_le_sinh_iff).mpr (Real.log_nonneg hu1)
        have hsinh : Real.sinh (Real.log u) = (u - 1 / u) / 2 := by
          rw [Real.sinh_eq, Real.exp_log hupos, Real.exp_neg, Real.exp_log hupos]; ring
        rwa [hsinh] at key
      have hmul := mul_le_mul_of_nonneg_left hlogle (le_of_lt (by positivity : (0 : ℝ) < 2 * u))
      have hrw2 : 2 * u * ((u - 1 / u) / 2) = u ^ 2 - 1 := by
        have e : 2 * u * ((u - 1 / u) / 2) = u * u - u * (1 / u) := by ring
        rw [e, hkey]; ring
      calc 2 * u * Real.log u ≤ 2 * u * ((u - 1 / u) / 2) := hmul
        _ = u ^ 2 - 1 := hrw2
    rw [hlog, hg_eq, div_le_div_iff₀ hab_pos (by positivity : (0 : ℝ) < b * u)]
    have hab_eq : a - b = b * (u ^ 2 - 1) := by rw [ha_eq]; ring
    rw [hab_eq]
    nlinarith [mul_le_mul_of_nonneg_left hstep (le_of_lt hb)]
  · -- HM ≤ GM : 1/√(ab) ≤ (a⁻¹+b⁻¹)/2
    have hrhs : (a⁻¹ + b⁻¹) / 2 = (a + b) / (2 * (a * b)) := by field_simp; ring
    rw [hrhs, div_le_div_iff₀ hgpos (by positivity : (0 : ℝ) < 2 * (a * b))]
    nlinarith [hg2, mul_le_mul_of_nonneg_right hAMGM (le_of_lt hgpos)]
  · -- density endpoint : (a⁻¹+b⁻¹)/2 ≤ 1/(ab) ⟺ a + b ≤ 2
    have hrhs : (a⁻¹ + b⁻¹) / 2 = (a + b) / (2 * (a * b)) := by field_simp; ring
    rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsum, mul_pos ha hb]

/-- **Lower reciprocal-mean tower.** For positive reals `a ≠ b` whose sum is at most `2`, the
reciprocal logarithmic-mean kernel `(log a − log b)/(a − b)` is bounded above, in turn, by the
reciprocal geometric kernel `1/√(ab)`, the reciprocal harmonic kernel `(a⁻¹ + b⁻¹)/2`, and the
reciprocal squared-geometric kernel `1/(ab)`. Reciprocating, this is `HM ≤ GM ≤ L` of the harmonic,
geometric and logarithmic means, together with the density endpoint `GM² ≤ HM`, which holds exactly
when `a + b ≤ 2`. The top link `2/(a + b) ≤ (log a − log b)/(a − b)` (`L ≤ A`) is recorded in the
sibling logarithmic-mean sandwich and is not restated here; the operator divergence tower this scalar
chain drives is likewise out of scope. -/
theorem mean_kernel_lower_tower {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b)
    (hsum : a + b ≤ 2) :
    (Real.log a - Real.log b) / (a - b) ≤ 1 / Real.sqrt (a * b)
    ∧ 1 / Real.sqrt (a * b) ≤ (a⁻¹ + b⁻¹) / 2
    ∧ (a⁻¹ + b⁻¹) / 2 ≤ 1 / (a * b) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have H := tower_ordered ha h (by linarith)
    obtain ⟨H2, H3, H4⟩ := H
    have eK : (Real.log b - Real.log a) / (b - a) = (Real.log a - Real.log b) / (a - b) := by
      rw [show Real.log b - Real.log a = -(Real.log a - Real.log b) from by ring,
          show b - a = -(a - b) from by ring, neg_div_neg_eq]
    have eP : b * a = a * b := by ring
    have eI : b⁻¹ + a⁻¹ = a⁻¹ + b⁻¹ := by ring
    rw [eK, eP] at H2
    rw [eP, eI] at H3
    rw [eI, eP] at H4
    exact ⟨H2, H3, H4⟩
  · exact tower_ordered hb h hsum

end D5.S3.Divergence.MeanKernels.MeanKernelLowerTower
