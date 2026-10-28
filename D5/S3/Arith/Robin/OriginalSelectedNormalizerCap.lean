/- GID: D5/S3/Arith/Robin/OriginalSelectedNormalizerCap
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalSelectedNormalizerCap
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Complete label budgets cap the literal selected volume and original kernel mass. -/

import D5.S3.Arith.Robin.OriginalFirstClockTransport
import D5.S3.Arith.Robin.OriginalMovingCutRow

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical Set MeasureTheory
open scoped BigOperators

namespace D5.S3.Arith.Robin.OriginalSelectedNormalizerCap

open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.Robin.OriginalMovingWindowMoment
open D5.S3.Arith.Robin.OriginalMovingCutRow
open D5.S3.Arith.Robin.MellinWeightedVariation (weight)
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g)

private theorem label_log_bounds (X : OriginalWindow) {p : ℕ} (hp : p ∈ X.labels) :
    Real.log (p : ℝ) ∈ Icc X.labelStart (2 * X.labelStart) := by
  rw [X.complete_labels] at hp
  obtain ⟨hp, hlo⟩ := Finset.mem_filter.mp hp
  have hhi : (p : ℝ) ≤ Real.exp (2 * X.labelStart) :=
    (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1).trans
      (Nat.floor_le (Real.exp_pos _).le)
  constructor
  · simpa using Real.log_le_log (Real.exp_pos X.labelStart) hlo
  · simpa using Real.log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos) hhi

private theorem edge_length (X : OriginalWindow) {p r : ℕ} (he : GoodEdge X p r) :
    Real.log (canonicalSource r : ℝ) - Real.log (canonicalSource p : ℝ) =
      Real.log (r : ℝ) - Real.log (p : ℝ) := by
  obtain ⟨U, hU, _, hpU, hrU, _⟩ := he.2.2.2.2
  rw [hpU, hrU, Nat.cast_mul, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (X.prime_labels r he.2.1).ne_zero)
      (by exact_mod_cast hU.ne'),
    Real.log_mul (by exact_mod_cast (X.prime_labels p he.1).ne_zero)
      (by exact_mod_cast hU.ne')]
  ring

private theorem edge_clock_four (X : OriginalWindow) {p r : ℕ} (he : GoodEdge X p r) :
    4 ≤ Real.log (canonicalSource p : ℝ) := by
  obtain ⟨U, hU, hcore, hpU, _⟩ := he.2.2.2.2
  have hcorele := Nat.le_of_dvd hU hcore
  have hN : (64 : ℝ) ≤ canonicalSource p := by
    rw [hpU]
    exact_mod_cast (show 64 ≤ p * U by nlinarith [(X.prime_labels p he.1).two_le])
  have hlog : 4 ≤ Real.log (64 : ℝ) := by
    have h := Real.log_pow (2 : ℝ) 6
    norm_num at h
    linarith [Real.log_two_gt_d9]
  exact hlog.trans (Real.log_le_log (by norm_num) hN)

private theorem kernel_density_cap {t x : ℝ} (ht : 4 ≤ t) (hx : 4 ≤ x) :
    kernel t x ≤ x ^ (-3 / 10 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := by linarith
  by_cases hactive : t < x ∧ x ≤ endpoint t
  · have hw : 0 < weight t := weight_pos (by linarith)
    have htden : 0 < t ^ (11 / 10 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have hwidth : width t ≤ t := by
      simpa [width] using Real.rpow_le_rpow_of_exponent_le
        (show 1 ≤ t by linarith) (show (4 / 5 : ℝ) ≤ 1 by norm_num)
    have hq : 1 ≤ x / t := (one_le_div ht0).mpr hactive.1.le
    have hpow : x ^ (3 / 10 : ℝ) ≤ t ^ (3 / 10 : ℝ) * (x / t) := by
      calc
        _ = t ^ (3 / 10 : ℝ) * (x / t) ^ (3 / 10 : ℝ) := by
          rw [← Real.mul_rpow ht0.le (div_pos hx0 ht0).le]
          congr 1
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (by simpa using Real.rpow_le_rpow_of_exponent_le hq
            (show (3 / 10 : ℝ) ≤ 1 by norm_num)) (Real.rpow_nonneg ht0.le _)
    have htriangle : (endpoint t - x) * (x / t) ≤ width t := by
      apply (le_div_iff₀ ht0).mp
      have heq : (endpoint t - x) * (x / t) * t = (t + width t - x) * x := by
        dsimp [endpoint]
        field_simp
      rw [heq]
      nlinarith [mul_nonneg (sub_nonneg.mpr hactive.1.le) (sub_nonneg.mpr hwidth)]
    have hproduct : (endpoint t - x) * x ^ (3 / 10 : ℝ) ≤ t ^ (11 / 10 : ℝ) := by
      calc
        _ ≤ (endpoint t - x) * (t ^ (3 / 10 : ℝ) * (x / t)) :=
          mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr hactive.2)
        _ = t ^ (3 / 10 : ℝ) * ((endpoint t - x) * (x / t)) := by ring
        _ ≤ t ^ (3 / 10 : ℝ) * width t :=
          mul_le_mul_of_nonneg_left htriangle (Real.rpow_nonneg ht0.le _)
        _ = t ^ (11 / 10 : ℝ) := by
          rw [width, ← Real.rpow_add ht0]
          norm_num
    have htriangleCap : (endpoint t - x) / t ^ (11 / 10 : ℝ) ≤ x ^ (-3 / 10 : ℝ) := by
      rw [show (-3 / 10 : ℝ) = -(3 / 10 : ℝ) by ring, Real.rpow_neg hx0.le]
      apply (div_le_iff₀ htden).mpr
      apply (le_inv_mul_iff₀ (Real.rpow_pos_of_pos hx0 (3 / 10 : ℝ))).mpr
      nlinarith [hproduct]
    calc
      kernel t x = (g x - g (endpoint t)) / (weight t * t ^ (11 / 10 : ℝ)) :=
        if_pos hactive
      _ ≤ (weight t * (endpoint t - x)) / (weight t * t ^ (11 / 10 : ℝ)) :=
        div_le_div_of_nonneg_right (price_drop ht hactive.1.le hactive.2).2
          (mul_pos hw htden).le
      _ = (endpoint t - x) / t ^ (11 / 10 : ℝ) := by field_simp
      _ ≤ _ := htriangleCap
  · rw [kernel, if_neg hactive]
    exact Real.rpow_nonneg hx0.le _

end D5.S3.Arith.Robin.OriginalSelectedNormalizerCap
