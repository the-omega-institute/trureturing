/- GID: D5/S3/Arith/CharacterSums/PascadiSeventhHeightRange
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiSeventhHeightRange
   mirror-E: none(waiver:actual-seventh-height-range)
   anchors: []
   utility: none
   digest: Strict area exponents supply the actual seventh-height gap. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! These numerical implications are used by the actual endpoint counting
pipeline. They supply no endpoint or counting estimates as hypotheses. -/

namespace D5.S3.Arith.CharacterSums.Original

/-- The largest of the actual residual, quadratic and mixed resultant constants. -/
def seventhHeightConstant : ℝ :=
  max (10368 * (3 : ℝ) ^ 9) (max 14256 (24 * (8 * (18 : ℝ)) ^ 4))

/-- The earlier eighth-height cutoff implies seventh height whenever the
actual coordinate area is at least one. -/
theorem seventh_height_gap_of_old_cutoffs (B M p : ℝ) (hp : 0 < p)
    (hB : 1 ≤ B) (hcap : B ^ 5 ≤ M ^ 5 * p ^ 3)
    (hlargeQ : (24 * (8 * (18 : ℝ)) ^ 4) ^ 5 * M ^ 40 < p) :
    seventhHeightConstant * B ^ 7 < p ^ 5 := by
  have hK : seventhHeightConstant = 24 * (8 * (18 : ℝ)) ^ 4 := by
    norm_num [seventhHeightConstant]
  have hK0 : 0 ≤ seventhHeightConstant := by rw [hK]; positivity
  have hB0 : 0 ≤ B := by linarith
  have hpow : (seventhHeightConstant * B ^ 8) ^ 5 ≤
      seventhHeightConstant ^ 5 * M ^ 40 * p ^ 24 := by
    calc
      _ = seventhHeightConstant ^ 5 * (B ^ 5) ^ 8 := by ring
      _ ≤ seventhHeightConstant ^ 5 * (M ^ 5 * p ^ 3) ^ 8 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hcap 8) (by positivity)
      _ = _ := by ring
  have hlarge : seventhHeightConstant ^ 5 * M ^ 40 < p := by
    simpa only [hK] using hlargeQ
  have hstrict : (seventhHeightConstant * B ^ 8) ^ 5 < (p ^ 5) ^ 5 := by
    calc
      _ ≤ seventhHeightConstant ^ 5 * M ^ 40 * p ^ 24 := hpow
      _ < p * p ^ 24 := mul_lt_mul_of_pos_right hlarge (pow_pos hp _)
      _ = _ := by ring
  have h8 : seventhHeightConstant * B ^ 8 < p ^ 5 :=
    (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : 5 ≠ 0)).mp hstrict
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hB (by decide : 7 ≤ 8)) hK0).trans_lt h8

/-- The seventh-height gap also supplies the small-coordinate separations
needed by the zero-reduction branch and the enlarged number-field envelope. -/
theorem seventh_height_basic_bounds (p I J : ℝ) (hp : 0 < p)
    (hJI : J ≤ I) (hJ : 1 ≤ J)
    (hgap : seventhHeightConstant * (I * J) ^ 7 < p ^ 5) :
    18 ≤ p ∧ 8 * I * J < p ∧ 6 * I ^ 3 < p ^ 3 ∧ I ≤ p := by
  have hI : 1 ≤ I := hJ.trans hJI
  have hI0 : 0 ≤ I := by linarith
  have hB : 1 ≤ I * J := one_le_mul_of_one_le_of_one_le hI hJ
  have hK18 : (18 : ℝ) ^ 5 ≤ seventhHeightConstant := by
    norm_num [seventhHeightConstant]
  have hK8 : (8 : ℝ) ^ 7 ≤ seventhHeightConstant := by
    norm_num [seventhHeightConstant]
  have hK0 : 0 ≤ seventhHeightConstant := hK18.trans' (by norm_num)
  have h18pow : (18 : ℝ) ^ 5 < p ^ 5 :=
    (hK18.trans (le_mul_of_one_le_right hK0 (one_le_pow₀ hB))).trans_lt hgap
  have hp18 : 18 < p :=
    (pow_lt_pow_iff_left₀ (by norm_num) hp.le (by decide : 5 ≠ 0)).mp h18pow
  have hp1 : 1 ≤ p := by linarith
  have h8pow : (8 * (I * J)) ^ 7 < p ^ 7 := by
    calc
      _ = (8 : ℝ) ^ 7 * (I * J) ^ 7 := mul_pow _ _ _
      _ ≤ seventhHeightConstant * (I * J) ^ 7 :=
        mul_le_mul_of_nonneg_right hK8 (by positivity)
      _ < p ^ 5 := hgap
      _ ≤ p ^ 7 := pow_le_pow_right₀ hp1 (by decide : 5 ≤ 7)
  have hsmall : 8 * (I * J) < p :=
    (pow_lt_pow_iff_left₀ (by positivity) hp.le (by decide : 7 ≠ 0)).mp h8pow
  have hIB : I ≤ I * J := le_mul_of_one_le_right hI0 hJ
  have htwo : 2 * I < p := by linarith only [hsmall, hIB, hI]
  have hcubed := pow_lt_pow_left₀ htwo (by positivity : 0 ≤ 2 * I) (by decide : 3 ≠ 0)
  refine ⟨hp18.le, by nlinarith only [hsmall], ?_, by linarith only [htwo, hI]⟩
  nlinarith only [hcubed, pow_nonneg hI0 3]

/-- Every fixed area exponent below twenty-six sevenths supplies the literal
seventh-height gap beyond one threshold chosen before p and the area. -/
theorem seventh_area_height_cutoff (α C : ℝ) (hα : α < 26 / 7) (hC : 1 ≤ C) :
    ∃ P : ℝ, 0 < P ∧ ∀ p A : ℝ, P < p → 0 ≤ A → A ≤ C * p ^ α →
      seventhHeightConstant * (32 * (A / p ^ 3)) ^ 7 < p ^ 5 := by
  let d := 26 - 7*α
  have hd : 0 < d := by dsimp [d]; linarith
  let B := seventhHeightConstant * (32 * C) ^ 7
  have hK : 0 < seventhHeightConstant := by norm_num [seventhHeightConstant]
  have hB : 0 < B := by dsimp [B]; positivity
  let P := max 18 ((1 + B) ^ d⁻¹)
  refine ⟨P, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 18) (le_max_left _ _), ?_⟩
  intro p A hlarge hA harea
  have hp18 : 18 < p := (le_max_left _ _).trans_lt hlarge
  have hp : 0 < p := by linarith
  have hthreshold : (1 + B) ^ d⁻¹ < p := (le_max_right _ _).trans_lt hlarge
  have hBpow : B < p ^ d := by
    have hh := (Real.rpow_inv_lt_iff_of_pos (by positivity : 0 ≤ 1 + B) hp.le hd).mp
      hthreshold
    linarith only [hh]
  have hA7 : A ^ 7 ≤ C ^ 7 * p ^ (α*7) := by
    calc
      _ ≤ (C * p ^ α) ^ 7 := pow_le_pow_left₀ hA harea 7
      _ = C ^ 7 * (p ^ α) ^ 7 := mul_pow _ _ _
      _ = _ := by rw [← Real.rpow_mul_natCast hp.le]; norm_num
  have hbound : B * p ^ (α*7) < p ^ 26 := by
    calc
      _ < p ^ d * p ^ (α*7) := mul_lt_mul_of_pos_right hBpow (Real.rpow_pos_of_pos hp _)
      _ = p ^ (d+α*7) := (Real.rpow_add hp _ _).symm
      _ = p ^ 26 := by dsimp [d]; norm_num [show 26 - 7*α+α*7=(26 : ℝ) by ring]
  have hden : (p ^ 3) ^ 7 = p ^ 21 := by ring
  calc
    seventhHeightConstant * (32 * (A / p ^ 3)) ^ 7 =
        (seventhHeightConstant * 32 ^ 7 * A ^ 7) / p ^ 21 := by
      rw [mul_pow, div_pow, hden]
      ring
    _ ≤ (seventhHeightConstant * 32 ^ 7 * (C ^ 7 * p ^ (α*7))) / p ^ 21 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA7 (by positivity)) (by positivity)
    _ = (B * p ^ (α*7)) / p ^ 21 := by dsimp [B]; ring
    _ < p ^ 26 / p ^ 21 := div_lt_div_of_pos_right hbound (pow_pos hp _)
    _ = p ^ 5 := by field_simp

end D5.S3.Arith.CharacterSums.Original
