/- GID: D5/S3/Combinatorics/FairWindowAsymptotics
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FairWindowAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The optimal deterministic fair-window defect has reciprocal leading term one. -/

import D5.S3.Combinatorics.FairWindowUpperBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FairWindowAsymptotics

open Filter Asymptotics
open scoped Topology
open D5.S3.Combinatorics.FairWindowDefect
open D5.S3.Combinatorics.FairWindowUpperBound

set_option maxHeartbeats 1600000 in
-- Logarithmic word lengths combine the rational finite bounds with real asymptotics.
/-- Along the natural window lengths, the exact deterministic optimum differs
from 1/R by O(log R/R²), and its product with R converges to one. -/
theorem fair_window_defect_asymptotics :
    (fun R : ℕ => (optimalFairDefect R : ℝ) - 1 / (R : ℝ)) =O[atTop]
      (fun R : ℕ => Real.log R / (R : ℝ) ^ 2) ∧
    Tendsto (fun R : ℕ => (R : ℝ) * (optimalFairDefect R : ℝ)) atTop (𝓝 1) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := 4 / Real.log 2 + 8
  have hC : 0 < C := by dsimp [C]; positivity
  have hlog : (fun R : ℕ => Real.log R) =o[atTop] (fun R : ℕ => (R : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ R : ℕ in atTop, 2 ≤ R ∧ 1 ≤ Real.log R ∧
      C * Real.log R ≤ (R : ℝ) / 2 := by
    filter_upwards [eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
      hlog.bound (show (0 : ℝ) < 1 / (2 * C) by positivity)] with R hR hL hsmall
    change 1 ≤ Real.log (R : ℝ) at hL
    refine ⟨hR, hL, ?_⟩
    have hr : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    simp only [Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg (by linarith : 0 ≤ Real.log R)]
      at hsmall
    have he := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (show Real.log R ≤ (R : ℝ) / (2 * C) by simpa [div_eq_mul_inv, mul_comm] using hsmall)
    nlinarith
  let K : ℝ := 2 * C + 2
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound : ∀ᶠ R : ℕ in atTop,
      |(optimalFairDefect R : ℝ) - 1 / (R : ℝ)| ≤ K * Real.log R / (R : ℝ) ^ 2 := by
    filter_upwards [hlarge] with R hR
    obtain ⟨hR2, hL, hsmall⟩ := hR
    have hr : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
    have hr1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
    let m := 4 * (Nat.log 2 (R + 1) + 1)
    have hm : 1 ≤ m := by dsimp [m]; omega
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hmlog : (m : ℝ) ≤ C * Real.log R := by
      have hn := Real.natLog_le_logb (R + 1) 2
      have hlogadd : Real.log (R + 1 : ℝ) ≤ Real.log 2 + Real.log R := by
        calc
          _ ≤ Real.log (2 * (R : ℝ)) := Real.log_le_log (by positivity) (by linarith)
          _ = _ := Real.log_mul (by norm_num) hr.ne'
      have hdiv := (div_le_div_iff_of_pos_right hl2).mpr hlogadd
      have he : (Real.log 2 + Real.log R) / Real.log 2 =
          1 + Real.log R / Real.log 2 := by field_simp
      simp only [Real.logb, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hn
      rw [he] at hdiv
      have hmle : (m : ℝ) ≤ 4 * (Real.log R / Real.log 2 + 2) := by
        dsimp [m]
        push_cast
        linarith
      calc
        _ ≤ 4 * (Real.log R / Real.log 2 + 2) := hmle
        _ ≤ C * Real.log R := by
          dsimp [C]
          simp only [div_eq_mul_inv]
          nlinarith
    have hmhalf : (m : ℝ) ≤ (R : ℝ) / 2 := hmlog.trans hsmall
    have hmR : m ≤ R := by exact_mod_cast (show (m : ℝ) ≤ R by linarith)
    let N := R - m + 2
    have hN : (N : ℝ) = (R : ℝ) - m + 2 := by simp [N, Nat.cast_sub hmR]
    have hNpos : (0 : ℝ) < N := by rw [hN]; linarith
    have hNhalf : (R : ℝ) / 2 ≤ N := by rw [hN]; linarith
    have hNle : (N : ℝ) ≤ R + 1 := by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [hN]; linarith
    have hpow : ((R : ℝ) + 1) ^ 4 ≤ (2 : ℝ) ^ m := by
      have hn := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (R + 1)).le
      have hn' : (R : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 (R + 1) + 1) := by exact_mod_cast hn
      have hh := pow_le_pow_left₀ (show (0 : ℝ) ≤ R + 1 by positivity) hn' 4
      simpa [m, pow_mul, Nat.mul_comm] using hh
    have hcol : ((N.choose 2 : ℕ) : ℝ) / (2 : ℝ) ^ m ≤ 1 / (R : ℝ) ^ 2 := by
      have hchoose : ((N.choose 2 : ℕ) : ℝ) ≤ ((R : ℝ) + 1) ^ 2 := by
        calc
          _ ≤ (N : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow N 2
          _ ≤ ((R : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hNpos.le hNle 2
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ m) (sq_pos_of_pos hr)).mpr
      calc
        _ ≤ ((R : ℝ) + 1) ^ 2 * (R : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hchoose (sq_nonneg _)
        _ ≤ ((R : ℝ) + 1) ^ 4 := by nlinarith [sq_nonneg (R : ℝ)]
        _ ≤ _ := by simpa using hpow
    obtain ⟨f, hf⟩ := fair_window_defect_upper_bound R m hm hmR
    have hopt : optimalFairDefect R ≤ fairDefect R f :=
      Finset.inf'_le _ (Finset.mem_univ f)
    have hu : (optimalFairDefect R : ℝ) ≤ 1 / (N : ℝ) +
        ((N.choose 2 : ℕ) : ℝ) / (2 : ℝ) ^ m := by
      have h := hopt.trans hf
      have hc := (Rat.cast_le (K := ℝ)).mpr h
      push_cast at hc
      simpa only [N, hN] using hc
    have hl : 1 / ((R : ℝ) + 2) ≤ (optimalFairDefect R : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr (fair_window_defect_lower_bound R).2
      push_cast at h
      exact h
    have hrecip : 1 / (N : ℝ) - 1 / (R : ℝ) ≤ 2 * (m : ℝ) / (R : ℝ) ^ 2 := by
      have hid : 1 / (N : ℝ) - 1 / (R : ℝ) =
          ((m : ℝ) - 2) / ((R : ℝ) * N) := by
        field_simp
        nlinarith [hN]
      rw [hid]
      calc
        _ ≤ (m : ℝ) / ((R : ℝ) * N) := by
          apply div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ ≤ 2 * (m : ℝ) / (R : ℝ) ^ 2 := by
          apply (div_le_div_iff₀ (mul_pos hr hNpos) (sq_pos_of_pos hr)).mpr
          have hh : (R : ℝ) ^ 2 ≤ 2 * ((R : ℝ) * N) := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hh hm0]
    have hlow : -(2 / (R : ℝ) ^ 2) ≤ (optimalFairDefect R : ℝ) - 1 / (R : ℝ) := by
      have hh : -(2 / (R : ℝ) ^ 2) ≤ 1 / ((R : ℝ) + 2) - 1 / (R : ℝ) := by
        field_simp
        nlinarith
      linarith
    have hhigh : (optimalFairDefect R : ℝ) - 1 / (R : ℝ) ≤
        (2 * (m : ℝ) + 1) / (R : ℝ) ^ 2 := by
      have hh := add_le_add hu hcol
      have he : 2 * (m : ℝ) / (R : ℝ) ^ 2 + 1 / (R : ℝ) ^ 2 =
          (2 * (m : ℝ) + 1) / (R : ℝ) ^ 2 := by ring
      rw [← he]
      linarith
    have hKlog : 2 ≤ K * Real.log R := by dsimp [K]; nlinarith
    apply abs_le.mpr
    constructor
    · have hh := div_le_div_of_nonneg_right hKlog (sq_nonneg (R : ℝ))
      linarith
    · apply hhigh.trans
      apply div_le_div_of_nonneg_right _ (sq_nonneg (R : ℝ))
      dsimp [K]
      nlinarith
  have hbig : (fun R : ℕ => (optimalFairDefect R : ℝ) - 1 / (R : ℝ)) =O[atTop]
      (fun R : ℕ => Real.log R / (R : ℝ) ^ 2) := by
    apply Asymptotics.IsBigO.of_bound K
    filter_upwards [hbound] with R hR
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.log_natCast_nonneg R) (sq_nonneg _))]
    simpa [mul_div_assoc] using hR
  refine ⟨hbig, ?_⟩
  have hmult : (fun R : ℕ => (R : ℝ) * ((optimalFairDefect R : ℝ) - 1 / (R : ℝ))) =O[atTop]
      (fun R : ℕ => Real.log R / (R : ℝ)) := by
    have hh := (Asymptotics.isBigO_refl (fun R : ℕ => (R : ℝ)) atTop).mul hbig
    apply hh.congr_right
    intro R
    by_cases hR : (R : ℝ) = 0
    · simp [hR]
    · field_simp
  have hlim := hmult.trans_tendsto hlog.tendsto_div_nhds_zero
  have he : (fun R : ℕ => (R : ℝ) * (optimalFairDefect R : ℝ)) =ᶠ[atTop]
      (fun R : ℕ => (R : ℝ) * ((optimalFairDefect R : ℝ) - 1 / (R : ℝ)) + 1) := by
    filter_upwards [eventually_ge_atTop 1] with R hR
    have hr : (R : ℝ) ≠ 0 := by exact_mod_cast (show R ≠ 0 by omega)
    field_simp
    ring
  apply Filter.Tendsto.congr' he.symm
  simpa using hlim.add_const 1

#print axioms fair_window_defect_asymptotics

end D5.S3.Combinatorics.FairWindowAsymptotics
