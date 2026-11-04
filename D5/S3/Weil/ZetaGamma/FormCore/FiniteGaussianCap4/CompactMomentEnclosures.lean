/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMomentEnclosures
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Rational enclosures transported to actual compact Gaussian moments. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactHalfMoment
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.IntegerExpMoment

/-! Actual H, J and signed W moment enclosures, with the complete H0 tail. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace FiniteGaussianCap475
open MeasureTheory Set
open scoped BigOperators
open RHFiniteGaussian.AnalyticEndpoints

/-- A rational form of the positive H0 beta-series coefficient. -/
def H0TermQ (n : ℕ) : ℚ :=
  12 ^ n / ∏ j ∈ Finset.range (n + 1), (13 / 2 + (j : ℚ))
def H0PrefixQ : ℚ := ∑ n ∈ Finset.range 161, H0TermQ n
def H0TailQ : ℚ := H0TermQ 161 / (1 - 24 / 335)

def CLowerQ : ℚ := 6 ^ 6 * sqrt6Lower250 * expNeg12Lower250
def CUpperQ : ℚ := 6 ^ 6 * sqrt6Upper250 * expNeg12Upper250

def HLowerQ : ℕ → ℚ
  | 0 => CLowerQ * H0PrefixQ
  | m + 1 => ((m : ℚ) + 13 / 2) / 2 * HLowerQ m - 6 ^ m * CUpperQ / 2
def HUpperQ : ℕ → ℚ
  | 0 => CUpperQ * (H0PrefixQ + H0TailQ)
  | m + 1 => ((m : ℚ) + 13 / 2) / 2 * HUpperQ m - 6 ^ m * CLowerQ / 2

private theorem H0TermQ_cast (n : ℕ) :
    (H0TermQ n : ℝ) = momentTerm (11 / 2) 2 6 n := by
  simp only [H0TermQ, momentTerm, momentDenominator]
  push_cast
  congr 2 <;> norm_num

private theorem H0TermQ_nonneg (n : ℕ) : 0 ≤ H0TermQ n := by
  unfold H0TermQ
  apply div_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro j _
  positivity

private theorem H0PrefixQ_nonneg : 0 ≤ H0PrefixQ := by
  exact Finset.sum_nonneg (fun n _ => H0TermQ_nonneg n)
private theorem H0TailQ_nonneg : 0 ≤ H0TailQ := by
  exact div_nonneg (H0TermQ_nonneg _) (by norm_num)

private theorem six_half_power :
    (6 : ℝ) ^ (13 / 2 : ℝ) = 6 ^ 6 * Real.sqrt 6 := by
  rw [show (13 / 2 : ℝ) = 6 + 1 / 2 by norm_num, Real.rpow_add (by norm_num)]
  norm_num only [Real.rpow_natCast, ← Real.sqrt_eq_rpow]

private theorem C_bounds :
    (CLowerQ : ℝ) ≤ (6 : ℝ) ^ (13 / 2 : ℝ) * Real.exp (-12) ∧
    (6 : ℝ) ^ (13 / 2 : ℝ) * Real.exp (-12) ≤ (CUpperQ : ℝ) := by
  have hs := sqrt_six_250_bounds
  have he := exp_neg_twelve_250_bounds
  have hl0 : (0 : ℝ) ≤ (sqrt6Lower250 : ℝ) := by norm_num [sqrt6Lower250]
  have hu0 : (0 : ℝ) ≤ (sqrt6Upper250 : ℝ) := by norm_num [sqrt6Upper250]
  have hel0 : (0 : ℝ) ≤ (expNeg12Lower250 : ℝ) := by norm_num [expNeg12Lower250]
  have heu0 : (0 : ℝ) ≤ (expNeg12Upper250 : ℝ) := by norm_num [expNeg12Upper250]
  rw [six_half_power]
  simp only [CLowerQ, CUpperQ, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  constructor
  · exact mul_le_mul (mul_le_mul_of_nonneg_left hs.1 (by positivity)) he.1
      hel0 (by positivity)
  · exact mul_le_mul (mul_le_mul_of_nonneg_left hs.2 (by positivity)) he.2
      (Real.exp_nonneg _) (by positivity)

private theorem H0_bounds : (HLowerQ 0 : ℝ) ≤ H 0 ∧ H 0 ≤ (HUpperQ 0 : ℝ) := by
  have hb := H0_prefix_bounds 160 (by norm_num)
  have hp : (H0PrefixQ : ℝ) =
      ∑ n ∈ Finset.range 161, momentTerm (11 / 2) 2 6 n := by
    simp only [H0PrefixQ, Rat.cast_sum, H0TermQ_cast]
  have ht : (H0TailQ : ℝ) = momentTerm (11 / 2) 2 6 161 / (1 - 24 / 335) := by
    simp only [H0TailQ, Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat,
      H0TermQ_cast]
  have hp0 : (0 : ℝ) ≤ (H0PrefixQ : ℝ) := by exact_mod_cast H0PrefixQ_nonneg
  have ht0 : (0 : ℝ) ≤ (H0TailQ : ℝ) := by exact_mod_cast H0TailQ_nonneg
  norm_num only [show (160 : ℝ) + 15 / 2 = 335 / 2 by norm_num,
    show (12 : ℝ) / (335 / 2) = 24 / 335 by norm_num] at hb
  change _ * _ ≤ H 0 ∧ H 0 ≤ _ * _ at hb
  rw [mul_comm (Real.exp (-12))] at hb
  constructor
  · change ((CLowerQ * H0PrefixQ : ℚ) : ℝ) ≤ _
    push_cast
    exact (mul_le_mul_of_nonneg_right C_bounds.1 hp0).trans (by simpa [hp] using hb.1)
  · change _ ≤ ((CUpperQ * (H0PrefixQ + H0TailQ) : ℚ) : ℝ)
    push_cast
    apply le_trans ?_ (mul_le_mul_of_nonneg_right C_bounds.2 (add_nonneg hp0 ht0))
    simpa [hp, ht, show (1 : ℝ) - 24 / 335 = 311 / 335 by norm_num] using hb.2

/-- Every real H moment is enclosed; no truncation index is a premise. -/
theorem H_bounds (m : ℕ) : (HLowerQ m : ℝ) ≤ H m ∧ H m ≤ (HUpperQ m : ℝ) := by
  induction m with
  | zero => exact H0_bounds
  | succ m ih =>
    have hpow : (6 : ℝ) ^ ((m : ℝ) + 13 / 2) =
        (6 : ℝ) ^ m * (6 : ℝ) ^ (13 / 2 : ℝ) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
    rw [H_succ, hpow]
    simp only [HLowerQ, HUpperQ, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
      Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_pow]
    have hc := C_bounds
    have hk : (0 : ℝ) ≤ ((m : ℝ) + 13 / 2) / 2 := by positivity
    have hr := mul_le_mul_of_nonneg_left hc.1 (show (0 : ℝ) ≤ 6 ^ m by positivity)
    have hr' := mul_le_mul_of_nonneg_left hc.2 (show (0 : ℝ) ≤ 6 ^ m by positivity)
    have hl := mul_le_mul_of_nonneg_left ih.1 hk
    have hu := mul_le_mul_of_nonneg_left ih.2 hk
    constructor
    · simpa only [mul_assoc] using sub_le_sub hl
        (div_le_div_of_nonneg_right hr' (by norm_num : (0 : ℝ) ≤ 2))
    · simpa only [mul_assoc] using sub_le_sub hu
        (div_le_div_of_nonneg_right hr (by norm_num : (0 : ℝ) ≤ 2))

/-- Rational endpoint polynomial, retaining all integer powers. -/
def JSumQ (m : ℕ) (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (m + 1), (2 * x) ^ j / (j.factorial : ℚ)
def JLowerQ (m : ℕ) : ℚ :=
  (m.factorial : ℚ) / 2 ^ (m + 1) *
    (expNegTwoPiLower250 * JSumQ m piLower250 - expNeg12Upper250 * JSumQ m 6)
def JUpperQ (m : ℕ) : ℚ :=
  (m.factorial : ℚ) / 2 ^ (m + 1) *
    (expNegTwoPiUpper250 * JSumQ m piUpper250 - expNeg12Lower250 * JSumQ m 6)

private theorem JSumQ_nonneg (m : ℕ) {x : ℚ} (hx : 0 ≤ x) : 0 ≤ JSumQ m x := by
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (pow_nonneg (by positivity) _) (Nat.cast_nonneg _)

private theorem JSumQ_cast (m : ℕ) (x : ℚ) :
    (JSumQ m x : ℝ) = ∑ j ∈ Finset.range (m + 1), (2 * (x : ℝ)) ^ j /
      (j.factorial : ℝ) := by
  unfold JSumQ
  push_cast
  rfl

private theorem JSum_mono (m : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (∑ j ∈ Finset.range (m + 1), (2 * x) ^ j / (j.factorial : ℝ)) ≤
    ∑ j ∈ Finset.range (m + 1), (2 * y) ^ j / (j.factorial : ℝ) := by
  apply Finset.sum_le_sum
  intro j _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact pow_le_pow_left₀ (by positivity) (by linarith) j

/-- Actual nonnegative integrals, also needed to transport variable W coefficients. -/
theorem J_nonneg (m : ℕ) : 0 ≤ J m := by
  have hp6 : Real.pi ≤ 6 := le_trans Real.pi_le_four (by norm_num)
  apply intervalIntegral.integral_nonneg hp6
  intro x hx
  exact mul_nonneg (pow_nonneg (Real.pi_pos.le.trans hx.1) _) (Real.exp_nonneg _)

/-- The finite endpoint formula transports the proved analytic boxes to every J_m. -/
theorem J_bounds (m : ℕ) : (JLowerQ m : ℝ) ≤ J m ∧ J m ≤ (JUpperQ m : ℝ) := by
  have hp := pi_250_bounds
  have he := exp_neg_two_pi_250_bounds
  have hf := exp_neg_twelve_250_bounds
  have hpl : (0 : ℝ) ≤ (piLower250 : ℝ) := by norm_num [piLower250]
  have hsl := JSum_mono m hpl hp.1
  have hsu := JSum_mono m Real.pi_pos.le hp.2
  have hS0 (x : ℝ) (hx : 0 ≤ x) :
      0 ≤ ∑ j ∈ Finset.range (m + 1), (2 * x) ^ j / (j.factorial : ℝ) := by
    apply Finset.sum_nonneg
    intro j _
    positivity
  have hel0 : (0 : ℝ) ≤ (expNegTwoPiLower250 : ℝ) := by
    norm_num [expNegTwoPiLower250]
  have heh0 : (0 : ℝ) ≤ (expNegTwoPiUpper250 : ℝ) := by
    norm_num [expNegTwoPiUpper250]
  have hfl0 : (0 : ℝ) ≤ (expNeg12Lower250 : ℝ) := by norm_num [expNeg12Lower250]
  have hfh0 : (0 : ℝ) ≤ (expNeg12Upper250 : ℝ) := by norm_num [expNeg12Upper250]
  have hl := mul_le_mul he.1 hsl (hS0 _ hpl) (Real.exp_nonneg _)
  have hu := mul_le_mul he.2 hsu (hS0 _ Real.pi_pos.le) heh0
  have htl := mul_le_mul_of_nonneg_right hf.1 (hS0 6 (by norm_num))
  have htu := mul_le_mul_of_nonneg_right hf.2 (hS0 6 (by norm_num))
  simp only [show (2 : ℝ) * 6 = 12 by norm_num] at htl htu
  rw [(J_endpoint m).2]
  simp only [JLowerQ, JUpperQ, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_pow, JSumQ_cast]
  have hk : (0 : ℝ) ≤ (m.factorial : ℝ) / 2 ^ (m + 1) := by positivity
  constructor
  · apply mul_le_mul_of_nonneg_left _ hk
    simpa only [neg_mul, show (2 : ℝ) * 6 = 12 by norm_num] using sub_le_sub hl htu
  · apply mul_le_mul_of_nonneg_left _ hk
    simpa only [neg_mul, show (2 : ℝ) * 6 = 12 by norm_num] using sub_le_sub hu htl

/-- Coefficients of the signed moment contraction. -/
def ALowerQ : ℚ := 1 / (piUpper250 ^ 2 * sqrtPiUpper250)
def AUpperQ : ℚ := 1 / (piLower250 ^ 2 * sqrtPiLower250)
def BLowerQ : ℚ := 4 * piLower250 ^ 3 * sqrtPiLower250
def BUpperQ : ℚ := 4 * piUpper250 ^ 3 * sqrtPiUpper250

def W (m : ℕ) : ℝ := H m / 10 -
  (1 / (Real.pi ^ 2 * Real.sqrt Real.pi)) * J (m + 6) +
  (4 * Real.pi ^ 3 * Real.sqrt Real.pi) * J m

def WLowerQ (m : ℕ) : ℚ := HLowerQ m / 10 - AUpperQ * JUpperQ (m + 6) +
  BLowerQ * JLowerQ m
def WUpperQ (m : ℕ) : ℚ := HUpperQ m / 10 - ALowerQ * JLowerQ (m + 6) +
  BUpperQ * JUpperQ m

private theorem AB_bounds :
    (0 : ℝ) ≤ (ALowerQ : ℝ) ∧ (0 : ℝ) ≤ (AUpperQ : ℝ) ∧
    (0 : ℝ) ≤ (BLowerQ : ℝ) ∧ (0 : ℝ) ≤ (BUpperQ : ℝ) ∧
    ((ALowerQ : ℝ) ≤ 1 / (Real.pi ^ 2 * Real.sqrt Real.pi) ∧
      1 / (Real.pi ^ 2 * Real.sqrt Real.pi) ≤ (AUpperQ : ℝ)) ∧
    ((BLowerQ : ℝ) ≤ 4 * Real.pi ^ 3 * Real.sqrt Real.pi ∧
      4 * Real.pi ^ 3 * Real.sqrt Real.pi ≤ (BUpperQ : ℝ)) := by
  have hp := pi_250_bounds
  have hs := sqrt_pi_250_bounds
  have hpl : (0 : ℝ) < (piLower250 : ℝ) := by norm_num [piLower250]
  have hpu : (0 : ℝ) < (piUpper250 : ℝ) := by norm_num [piUpper250]
  have hsl : (0 : ℝ) < (sqrtPiLower250 : ℝ) := by norm_num [sqrtPiLower250]
  have hsu : (0 : ℝ) < (sqrtPiUpper250 : ℝ) := by norm_num [sqrtPiUpper250]
  have hdp := mul_pos (pow_pos Real.pi_pos 2) (Real.sqrt_pos.2 Real.pi_pos)
  have hdl := mul_pos (pow_pos hpl 2) hsl
  have hdu := mul_pos (pow_pos hpu 2) hsu
  have hdlo := mul_le_mul (pow_le_pow_left₀ hpl.le hp.1 2) hs.1 hsl.le
    (pow_nonneg Real.pi_pos.le _)
  have hdhi := mul_le_mul (pow_le_pow_left₀ Real.pi_pos.le hp.2 2) hs.2
    (Real.sqrt_nonneg _) (pow_nonneg hpu.le _)
  simp only [ALowerQ, AUpperQ, BLowerQ, BUpperQ, Rat.cast_div, Rat.cast_one,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  refine ⟨by positivity, by positivity, by positivity, by positivity, ?_, ?_⟩
  · exact ⟨one_div_le_one_div_of_le hdp hdhi, one_div_le_one_div_of_le hdl hdlo⟩
  · constructor
    · exact mul_le_mul (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hpl.le hp.1 3) (by norm_num)) hs.1 hsl.le (by positivity)
    · exact mul_le_mul (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ Real.pi_pos.le hp.2 3) (by norm_num)) hs.2
        (Real.sqrt_nonneg _) (by positivity)

/-- All signed W moments, including odd indices, with no rational positivity premise. -/
theorem W_bounds (m : ℕ) : (WLowerQ m : ℝ) ≤ W m ∧ W m ≤ (WUpperQ m : ℝ) := by
  obtain ⟨ha0, ha1, hb0, hb1, ha, hb⟩ := AB_bounds
  have hj := J_bounds m
  have hj6 := J_bounds (m + 6)
  have hh := H_bounds m
  have hAlo : (ALowerQ : ℝ) * (JLowerQ (m + 6) : ℝ) ≤
      1 / (Real.pi ^ 2 * Real.sqrt Real.pi) * J (m + 6) :=
    (mul_le_mul_of_nonneg_left hj6.1 ha0).trans
      (mul_le_mul_of_nonneg_right ha.1 (J_nonneg _))
  have hAhi : 1 / (Real.pi ^ 2 * Real.sqrt Real.pi) * J (m + 6) ≤
      (AUpperQ : ℝ) * (JUpperQ (m + 6) : ℝ) :=
    (mul_le_mul_of_nonneg_right ha.2 (J_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hj6.2 ha1)
  have hBlo : (BLowerQ : ℝ) * (JLowerQ m : ℝ) ≤
      (4 * Real.pi ^ 3 * Real.sqrt Real.pi) * J m :=
    (mul_le_mul_of_nonneg_left hj.1 hb0).trans
      (mul_le_mul_of_nonneg_right hb.1 (J_nonneg _))
  have hBhi : (4 * Real.pi ^ 3 * Real.sqrt Real.pi) * J m ≤
      (BUpperQ : ℝ) * (JUpperQ m : ℝ) :=
    (mul_le_mul_of_nonneg_right hb.2 (J_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hj.2 hb1)
  simp only [WLowerQ, WUpperQ, W, Rat.cast_add, Rat.cast_sub, Rat.cast_div,
    Rat.cast_mul, Rat.cast_ofNat]
  constructor
  · exact add_le_add (sub_le_sub
      (div_le_div_of_nonneg_right hh.1 (by norm_num)) hAhi) hBlo
  · exact add_le_add (sub_le_sub
      (div_le_div_of_nonneg_right hh.2 (by norm_num)) hAlo) hBhi

end FiniteGaussianCap475
