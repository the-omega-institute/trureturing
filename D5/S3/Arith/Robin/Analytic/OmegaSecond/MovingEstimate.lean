/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp upper estimate for the moving prime remainder at square-root sharpness. -/

import D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight
import D5.S3.Arith.Robin.Analytic.OmegaSecond.ContinuumWeight
import D5.S3.Arith.Robin.Analytic.OmegaSecond.KernelLimit
import D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open MovingWeight KernelLimit

private lemma half_power (s : ℝ) : (1 / 2 : ℝ) ^ s = (2 : ℝ) ^ (-s) := by
  rw [div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2),
    one_rpow, one_div, rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

/-- Explicit central quadrature and geometric-tail majorant. -/
def majorant (P s : ℝ) : ℝ :=
  P / (s * log P) * correctionMajorant s +
    (s / 2 + 2) * P * (1 / 2 : ℝ) ^ s / log P +
    112 * log 2 * (P / log P ^ 2) +
    P * (1 / 2 : ℝ) ^ s + 2 * P * (2 / 3 : ℝ) ^ s

/-- The finite prime remainder is controlled uniformly in the endpoint x. -/
theorem remainder_le_majorant :
    ∀ᶠ P : ℝ in atTop, ∀ s : ℝ, π ≤ s → 2 ≤ s → ∀ x : ℝ,
      remainder P s x ≤ majorant P s := by
  classical
  filter_upwards [CentralWeight.central_prime_weight_upper,
    eventually_ge_atTop (2 : ℝ)] with P hcentral hP
  intro s hsπ hs x
  have hP0 : 0 < P := by linarith
  have hl : 0 < log P := log_pos (by linarith)
  have hs0 : 0 < s := by linarith
  let S := Nat.primesLE ⌊x⌋₊
  let A := S.filter (fun p : ℕ => (p : ℝ) ≤ P / 2)
  let B := S.filter (fun p : ℕ => P / 2 < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P)
  let C := S.filter (fun p : ℕ => 2 * P < (p : ℝ))
  have hpartition : remainder P s x =
      (∑ p ∈ A, weight P s p) + (∑ p ∈ B, weight P s p) +
        ∑ p ∈ C, weight P s p := by
    dsimp only [remainder, A, B, C, S]
    simp only [sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    by_cases hp1 : (p : ℝ) ≤ P / 2
    · have hp2 : ¬ 2 * P < (p : ℝ) := by linarith
      simp [hp1, hp2]
    · by_cases hp2 : (p : ℝ) ≤ 2 * P
      · simp [hp1, hp2, lt_of_not_ge hp1]
      · simp [hp1, hp2, lt_of_not_ge hp2]
  have hA : (∑ p ∈ A, weight P s p) ≤ P * (1 / 2 : ℝ) ^ s := by
    apply Tail.small_weight_tail hP hs0.le A
    intro p hp
    obtain ⟨hpS, hpP⟩ := mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hpS).2.pos, hpP⟩
  have hC : (∑ p ∈ C, weight P s p) ≤ 2 * P * (2 / 3 : ℝ) ^ s := by
    apply Tail.large_weight_tail hP hs C
    intro p hp
    exact (mem_filter.mp hp).2
  have hsub : B ⊆ primeInterval (P / 2) (2 * P) := by
    intro p hp
    obtain ⟨hpS, hpL, hpU⟩ := mem_filter.mp hp
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, (Nat.mem_primesLE.mp hpS).2⟩
    · exact (Nat.floor_lt (by positivity : 0 ≤ P / 2)).mpr hpL
    · exact (Nat.le_floor_iff (by positivity : 0 ≤ 2 * P)).mpr hpU
  have hB : (∑ p ∈ B, weight P s p) ≤
      (∫ t in (P / 2)..(2 * P), weight P s t) / log P +
        112 * log 2 * (P / log P ^ 2) := by
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => weight_nonneg _ _ _)).trans
      (hcentral s hs0.le)
  have hi := ContinuumWeight.central_integral_upper hP0 (by linarith : 1 < s)
  have hi' := div_le_div_of_nonneg_right hi hl.le
  rw [← half_power s] at hi'
  have hk := (kernel_correction_upper hsπ).2
  have hk' : P * (π / sin (π / s) - s) / log P ≤
      P / (s * log P) * correctionMajorant s := by
    have h := mul_le_mul_of_nonneg_left hk (div_nonneg hP0.le (mul_pos hs0 hl).le)
    convert h using 1 <;> field_simp [hs0.ne', hl.ne'] <;> ring
  rw [hpartition]
  dsimp only [majorant]
  have h := add_le_add (add_le_add hA hB) hC
  linarith only [h, hi', hk']

private lemma sharpness_top {c : ℝ} (hc : 0 < c) :
    Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop :=
  (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc

/-- The explicit majorant has the sharp normalized upper coefficient. -/
theorem majorant_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun P : ℝ => majorant P (c * sqrt (log P)) /
      (P / (log P * sqrt (log P)))) atTop (𝓝 (π ^ 2 / (6 * c))) := by
  have hhalf := (Tail.geometric_sqrt_decay hc
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).comp tendsto_log_atTop
  have hthird := (Tail.geometric_sqrt_decay hc
    (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)).comp tendsto_log_atTop
  have hsqrt : Tendsto (fun P : ℝ => 1 / sqrt (log P)) atTop (𝓝 0) :=
    (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_div_atTop 1
  have hlog : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop 1
  have hmain := (correction_majorant_limit.comp (sharpness_top hc)).div_const c
  have hcontinuum := hhalf.mul ((hsqrt.const_mul (c / 2)).add (hlog.const_mul 2))
  have hcount := hsqrt.const_mul (112 * log 2)
  have h := ((((hmain.add hcontinuum).add hcount).add hhalf).add (hthird.const_mul 2))
  norm_num only [mul_zero, zero_add, add_zero] at h
  convert h.congr' (show _ =ᶠ[atTop] _ from ?_) using 1
  · ring
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hP0 : P ≠ 0 := by linarith
    have hl := log_pos hP
    have hs := sqrt_pos.mpr hl
    change correctionMajorant (c * sqrt (log P)) / c +
        (log P * sqrt (log P) * (1 / 2 : ℝ) ^ (c * sqrt (log P))) *
          (c / 2 * (1 / sqrt (log P)) + 2 * (1 / log P)) +
        112 * log 2 * (1 / sqrt (log P)) +
        log P * sqrt (log P) * (1 / 2 : ℝ) ^ (c * sqrt (log P)) +
        2 * (log P * sqrt (log P) * (2 / 3 : ℝ) ^ (c * sqrt (log P))) =
      majorant P (c * sqrt (log P)) / (P / (log P * sqrt (log P)))
    dsimp only [majorant]
    field_simp [hP0, hl.ne', hs.ne', hc.ne']
    nlinarith [sq_sqrt hl.le]

/-- At square-root logarithmic sharpness, the finite prime remainder has the
sharp upper coefficient pi squared divided by six c, uniformly in x. -/
theorem moving_weight_upper {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ P : ℝ in atTop, ∀ x : ℝ,
      remainder P (c * sqrt (log P)) x ≤
        (π ^ 2 / (6 * c) + ε) * (P / (log P * sqrt (log P))) := by
  filter_upwards [remainder_le_majorant,
    (sharpness_top hc).eventually_ge_atTop π,
    (sharpness_top hc).eventually_ge_atTop 2,
    (majorant_limit hc).eventually_lt_const (by linarith :
      π ^ 2 / (6 * c) < π ^ 2 / (6 * c) + ε),
    eventually_gt_atTop (1 : ℝ)] with P hbound hsπ hs hlimit hP
  intro x
  refine (hbound _ hsπ hs x).trans ?_
  have hscale : 0 < P / (log P * sqrt (log P)) := by
    have := log_pos hP
    positivity
  exact ((div_lt_iff₀ hscale).mp hlimit).le

end D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate
