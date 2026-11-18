/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalRangeCutoffs
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalRangeCutoffs
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: The original area cap supplies all numerical long-chart separation cutoffs. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The original area exponent gives the fifth-power height cap exactly.
A uniform explicit large-parameter threshold supplies the remaining strict
separations. No chart, height or counting estimate is assumed. -/

namespace D5.S3.Arith.CharacterSums.Original

/-- In the original area range, the actual long-chart heights obey the endpoint
cap with M=32C. The explicit threshold also supplies every numerical separation
used by the bad-degree average; the bounded small-parameter range is separate. -/
theorem original_range_numeric_cutoffs {C p A : ℝ}
    (hC : 1 ≤ C) (hA : 0 ≤ A)
    (harea : A ≤ C*p^((18 : ℝ)/5))
    (hlarge : ((2 : ℝ)^20*(1+C))^200 < p) :
    (32*(A/p^3))^5 ≤ (32*C)^5*p^3 ∧
      A < p^4 ∧
      (10368*(3 : ℝ)^9)^5*(32*C)^35 < p^4 ∧
      (24*(8*(18 : ℝ))^4)^5*(32*C)^40 < p := by
  let D := (2 : ℝ)^20*(1+C)
  have hC0 : 0 ≤ C := by linarith
  have hD20 : (2 : ℝ)^20 ≤ D := by dsimp [D]; norm_num; linarith
  have hD1 : 1 ≤ D := (by norm_num : (1 : ℝ) ≤ 2^20).trans hD20
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hCD : C ≤ D := by dsimp [D]; norm_num; linarith
  have h32CD : 32*C ≤ D := by dsimp [D]; norm_num; linarith
  have hlarge' : D^200 < p := hlarge
  have hp1 : 1 ≤ p := (one_le_pow₀ hD1).trans hlarge'.le
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hrpow5 : (p^((18 : ℝ)/5))^5 = p^18 := by
    rw [← Real.rpow_mul_natCast hp0.le]
    norm_num
  have hA5 : A^5 ≤ C^5*p^18 := by
    calc
      A^5 ≤ (C*p^((18 : ℝ)/5))^5 := pow_le_pow_left₀ hA harea 5
      _ = C^5*p^18 := by rw [mul_pow, hrpow5]
  have hcap : (32*(A/p^3))^5 ≤ (32*C)^5*p^3 := by
    calc
      _ = (32 : ℝ)^5*(A^5/(p^3)^5) := by rw [mul_pow, div_pow]
      _ ≤ (32 : ℝ)^5*((C^5*p^18)/(p^3)^5) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hA5 (by positivity)) (by norm_num)
      _ = _ := by field_simp [hp0.ne']
  have hC5p : C^5 < p := by
    calc
      C^5 ≤ D^5 := pow_le_pow_left₀ hC0 hCD 5
      _ ≤ D^200 := pow_le_pow_right₀ hD1 (by decide : 5 ≤ 200)
      _ < p := hlarge'
  have hC5p2 : C^5 < p^2 := hC5p.trans_le (by nlinarith)
  have hA5strict : A^5 < (p^4)^5 := by
    calc
      _ ≤ C^5*p^18 := hA5
      _ < p^2*p^18 := mul_lt_mul_of_pos_right hC5p2 (pow_pos hp0 18)
      _ = _ := by ring
  have hAp4 : A < p^4 :=
    (pow_lt_pow_iff_left₀ hA (pow_nonneg hp0.le 4) (by decide : 5 ≠ 0)).mp hA5strict
  have hD10 : ((2 : ℝ)^20)^10 ≤ D^10 := pow_le_pow_left₀ (by positivity) hD20 10
  have hKR : (10368*(3 : ℝ)^9)^5 ≤ D^10 :=
    (by norm_num : (10368*(3 : ℝ)^9)^5 ≤ ((2 : ℝ)^20)^10).trans hD10
  have hKQ : (24*(8*(18 : ℝ))^4)^5 ≤ D^10 :=
    (by norm_num : (24*(8*(18 : ℝ))^4)^5 ≤ ((2 : ℝ)^20)^10).trans hD10
  have hsep (K : ℝ) (hK : K ≤ D^10) (n : ℕ) (hn : 10+n ≤ 200) :
      K*(32*C)^n < p := by
    calc
      K*(32*C)^n ≤ D^10*D^n := mul_le_mul hK
        (pow_le_pow_left₀ (by positivity : 0 ≤ 32*C) h32CD n)
        (by positivity) (by positivity)
      _ = D^(10+n) := (pow_add D 10 n).symm
      _ ≤ D^200 := pow_le_pow_right₀ hD1 hn
      _ < p := hlarge'
  have hR : (10368*(3 : ℝ)^9)^5*(32*C)^35 < p^4 :=
    (hsep _ hKR 35 (by decide)).trans_le
      (by simpa only [pow_one] using pow_le_pow_right₀ hp1 (by decide : 1 ≤ 4))
  exact ⟨hcap, hAp4, hR, hsep _ hKQ 40 (by decide)⟩

end D5.S3.Arith.CharacterSums.Original
