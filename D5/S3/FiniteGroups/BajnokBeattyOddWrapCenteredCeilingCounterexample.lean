/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapCenteredCeilingCounterexample
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapCenteredCeilingCounterexample
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/BajnokBeattyOddWrapCenteredCeilingCounterexample.claim; result=D5/S3/FiniteGroups/BajnokBeattyOddWrapCenteredCeilingCounterexample.result; claim=D5/S3/FiniteGroups/BajnokBeattyOddWrapCenteredCeilingCounterexample.claim
   digest: Exact original threshold 55310 at p57425 refutes the universal centered-ceiling formula. -/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
import D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapCenteredCeilingCounterexample

open D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
open D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket
open D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing

private noncomputable def P17 (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 17, x ^ m / (Nat.factorial m : ℝ)

private noncomputable def U17 (x : ℝ) : ℝ :=
  P17 x + x ^ 17 * 18 / ((Nat.factorial 17 : ℝ) * 17)

private theorem exp_interval17 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < P17 x ∧ P17 x ≤ Real.exp x ∧ Real.exp x ≤ U17 x := by
  have hone : (1 : ℝ) ≤ P17 x := by
    calc
      1 = x ^ 0 / (Nat.factorial 0 : ℝ) := by simp
      _ ≤ P17 x :=
        Finset.single_le_sum (f := fun m : ℕ => x ^ m / (Nat.factorial m : ℝ))
          (fun m _ => by positivity) (show 0 ∈ Finset.range 17 by norm_num)
  refine ⟨lt_of_lt_of_le zero_lt_one hone, ?_, ?_⟩
  · exact Real.sum_le_exp_of_nonneg hx0 17
  · simpa only [U17, P17, Nat.cast_ofNat,
      show (17 : ℝ) + 1 = 18 by norm_num] using
      (Real.exp_bound' hx0 hx1 (n := 17) (by norm_num))

private theorem exp_neg_nine_mul (x : ℝ) :
    Real.exp (-9 * x) = 1 / (Real.exp x) ^ 9 := by
  have hmul : Real.exp (9 * x) = (Real.exp x) ^ 9 := by
    simpa only [Nat.cast_ofNat] using Real.exp_nat_mul x 9
  rw [show -9 * x = -(9 * x) by ring, Real.exp_neg, hmul, inv_eq_one_div]

private theorem gaussian_interval17 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    P17 x + 1 / (U17 x) ^ 9 ≤ gaussian x ∧
      gaussian x ≤ U17 x + 1 / (P17 x) ^ 9 := by
  obtain ⟨hp, hl, hu⟩ := exp_interval17 hx0 hx1
  have hrecLower := one_div_le_one_div_of_le (pow_pos (Real.exp_pos x) 9)
    (pow_le_pow_left₀ (Real.exp_pos x).le hu 9)
  have hrecUpper := one_div_le_one_div_of_le (pow_pos hp 9)
    (pow_le_pow_left₀ hp.le hl 9)
  constructor
  · rw [gaussian, exp_neg_nine_mul]
    exact add_le_add hl hrecLower
  · rw [gaussian, exp_neg_nine_mul]
    exact add_le_add hu hrecUpper

private theorem gaussian_lower_endpoint :
    (2 + 1 / 10 ^ 13 : ℝ) <
      gaussian (2 / (3 * (963166449 / 1000000000 : ℝ))) := by
  have h := (gaussian_interval17
    (x := 2 / (3 * (963166449 / 1000000000 : ℝ)))
    (by norm_num) (by norm_num)).1
  refine lt_of_lt_of_le ?_ h
  norm_num [P17, U17, Finset.sum_range_succ, Nat.factorial]

private theorem gaussian_upper_endpoint :
    gaussian (2 / (3 * (963166449003 / 1000000000000 : ℝ))) <
      (2 - 1 / 10 ^ 12 : ℝ) := by
  have h := (gaussian_interval17
    (x := 2 / (3 * (963166449003 / 1000000000000 : ℝ)))
    (by norm_num) (by norm_num)).2
  refine lt_of_le_of_lt h ?_
  norm_num [P17, U17, Finset.sum_range_succ, Nat.factorial]

private theorem alpha_rational_bounds :
    (963166449 / 1000000000 : ℝ) < alpha ∧
      alpha < (963166449003 / 1000000000000 : ℝ) := by
  have hspos : 0 < 3 * s_star := by
    linarith only [two_thirds_lt_s_star]
  have hleft : s_star < 2 / (3 * (963166449 / 1000000000 : ℝ)) := by
    apply (gaussian_strictMonoOn.lt_iff_lt two_thirds_lt_s_star.le
      (by norm_num : (2 / 3 : ℝ) ≤
        2 / (3 * (963166449 / 1000000000 : ℝ)))).mp
    rw [gaussian_s_star]
    have h := gaussian_lower_endpoint
    linarith only [h]
  have hright : 2 / (3 * (963166449003 / 1000000000000 : ℝ)) < s_star := by
    apply (gaussian_strictMonoOn.lt_iff_lt
      (by norm_num : (2 / 3 : ℝ) ≤
        2 / (3 * (963166449003 / 1000000000000 : ℝ)))
      two_thirds_lt_s_star.le).mp
    rw [gaussian_s_star]
    have h := gaussian_upper_endpoint
    linarith only [h]
  constructor
  · unfold alpha
    apply (lt_div_iff₀ hspos).2
    have h := (lt_div_iff₀ (by norm_num :
      0 < 3 * (963166449 / 1000000000 : ℝ))).mp hleft
    nlinarith only [h]
  · unfold alpha
    apply (div_lt_iff₀ hspos).2
    have h := (div_lt_iff₀ (by norm_num :
      0 < 3 * (963166449003 / 1000000000000 : ℝ))).mp hright
    nlinarith only [h]

private theorem rounding_window_57425 :
    (55310 : ℝ) < alpha * 57425 + 1 / 6 ∧
      alpha * 57425 + 1 / 6 < 55310 + 1 / (25 * 57425 : ℝ) := by
  obtain ⟨hl, hu⟩ := alpha_rational_bounds
  have hleft : (55310 : ℝ) <
      (963166449 / 1000000000 : ℝ) * 57425 + 1 / 6 := by norm_num
  have hright : (963166449003 / 1000000000000 : ℝ) * 57425 + 1 / 6 <
      55310 + 1 / (25 * 57425 : ℝ) := by norm_num
  constructor
  · linarith only [hl, hleft]
  · linarith only [hu, hright]

private theorem ceil_alpha_mul_57425_add_one_sixth :
    Int.ceil (alpha * 57425 + (1 / 6 : ℝ)) = 55311 := by
  obtain ⟨hl, hu⟩ := rounding_window_57425
  have hc : (1 / (25 * 57425 : ℝ)) < 1 := by norm_num
  apply Int.ceil_eq_iff.mpr
  constructor
  · norm_num
    linarith only [hl]
  · norm_num
    linarith only [hu, hc]

private theorem ceil_alpha_mul_57425_add_one_sixth_sub_correction :
    Int.ceil (alpha * 57425 + (1 / 6 : ℝ) - 1 / (25 * 57425 : ℝ)) = 55310 := by
  obtain ⟨hl, hu⟩ := rounding_window_57425
  have hc : (1 / (25 * 57425 : ℝ)) < 1 := by norm_num
  apply Int.ceil_eq_iff.mpr
  constructor
  · norm_num
    linarith only [hl, hc]
  · norm_num
    linarith only [hu]

private theorem original_threshold_lower_endpoint_57425 :
    (55309 : ℝ) < alpha * 57425 + 1 / 6 - 1 / (6 * 57425 : ℝ) := by
  have hl := alpha_rational_bounds.1
  have hn : (55309 : ℝ) <
      (963166449 / 1000000000 : ℝ) * 57425 + 1 / 6 -
        1 / (6 * 57425 : ℝ) := by norm_num
  linarith only [hl, hn]

/-- The full original sign criterion has threshold 55310 at p = 57425.
The centered ceiling is 55311, so it cannot give this original threshold. -/
theorem original_centered_ceiling_counterexample :
    2 < (55310 : ℕ) ∧
      (∀ t : ℕ, 2 ≤ t → t < 55310 →
        (original_return_pair 57425 t).2 < (original_return_pair 57425 t).1) ∧
      (original_return_pair 57425 55310).1 ≤ (original_return_pair 57425 55310).2 ∧
      (∀ t : ℕ, 55310 < t →
        (original_return_pair 57425 t).1 < (original_return_pair 57425 t).2) ∧
      Int.ceil (alpha * 57425 + (1 / 6 : ℝ)) = 55311 := by
  obtain ⟨T, hT, _⟩ := actual_odd_wrap_threshold_bracket 57425
    (by norm_num) (by exact ⟨28712, by norm_num⟩)
  rcases hT with ⟨hT2, hbefore, hat, hafter, hlower, hupper⟩
  have hlower' : alpha * 57425 + 1 / 6 - 1 / (6 * 57425 : ℝ) < (T : ℝ) := by
    simpa only [Int.cast_ofNat] using hlower
  have hTlowerR : (55309 : ℝ) < (T : ℝ) :=
    original_threshold_lower_endpoint_57425.trans hlower'
  have hTlower : 55310 ≤ T := by
    have hh : 55309 < T := by exact_mod_cast hTlowerR
    omega
  have hTupperZ : (T : ℤ) ≤ 55310 := by
    calc
      (T : ℤ) ≤ Int.ceil (alpha * 57425 + 1 / 6 - 1 / (25 * 57425 : ℝ)) := by
        simpa only [Int.cast_ofNat] using hupper
      _ = 55310 := ceil_alpha_mul_57425_add_one_sixth_sub_correction
  have hTeq : T = 55310 := by omega
  subst T
  exact ⟨hT2, hbefore, hat, hafter, ceil_alpha_mul_57425_add_one_sixth⟩

/-- The proposed exact centered-ceiling rule, with the full original sign
criterion and its original odd-integer parameter domain. -/
def claim : Prop :=
  ∀ (p : ℤ), 5 ≤ p → Odd p →
    ∃ T : ℕ, 2 < T ∧
      (∀ t : ℕ, 2 ≤ t → t < T →
        (original_return_pair p t).2 < (original_return_pair p t).1) ∧
      (original_return_pair p T).1 ≤ (original_return_pair p T).2 ∧
      (∀ t : ℕ, T < t →
        (original_return_pair p t).1 < (original_return_pair p t).2) ∧
      (T : ℤ) = Int.ceil (alpha*(p : ℝ)+(1/6 : ℝ))

/-- The exact certified threshold contradicts the universal proposed rule.
This is the designated utility refutation result; no extra premise is added. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨T,hT2,hbefore,hat,hafter,hceil⟩ :=
    h 57425 (by norm_num) (by exact ⟨28712,by norm_num⟩)
  have hc := original_centered_ceiling_counterexample
  have hTZ : (T : ℤ) = 55311 := by
    calc
      (T : ℤ) = Int.ceil (alpha*(57425 : ℝ)+(1/6 : ℝ)) := by
        simpa only [Int.cast_ofNat] using hceil
      _ = 55311 := hc.2.2.2.2
  have hT : T = 55311 := by exact_mod_cast hTZ
  have hclaimed : (original_return_pair 57425 55310).2 <
      (original_return_pair 57425 55310).1 := by
    simpa only [Nat.cast_ofNat] using (hbefore 55310 (by decide) (by omega))
  have hactual := hc.2.2.1
  exact (not_lt_of_ge hactual) hclaimed

end D5.S3.FiniteGroups.BajnokBeattyOddWrapCenteredCeilingCounterexample
