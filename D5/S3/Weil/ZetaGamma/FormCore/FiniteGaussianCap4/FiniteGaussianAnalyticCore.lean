/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianAnalyticCore
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual analytic input enclosures for the finite Gaussian cap certificate. -/

/-
SOURCE ONLY, UNCOMPILED. No acceptance or certificate-completion claim.
Analytic input suppliers for the SAME finiteGaussian signedV certificate.
Pinned API: Mathlib v4.35.0, 56a005855ea17e0b0958f73ec801ae140b0a1679.

Mathlib attribution: the arctan series is Jeremy Tan's; Machin's identity is
reused from Real.four_mul_arctan_inv_5_sub_arctan_inv_239. Alternating partial
sum bounds and the geometric HasSum bound are used as library theorems.
No checker, interval syntax, numerical evaluator, or certificate is defined.
The closed rational literals below are untrusted generated data; the proposed
proofs of their values and comparisons use ordinary norm_num proof production.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Actual analytic input enclosures for the finite Gaussian cap certificate. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
open Finset Filter
open scoped Topology

namespace RHFiniteGaussian.AnalyticEndpoints

/-- N terms, indexed 0 through N-1, of the actual real arctan series. -/
def atanPrefix (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 * n + 1 : ℕ)

/-- Its finite rational counterpart, without any rounded arithmetic. -/
def atanPrefixQ (x : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ range N, (-1 : ℚ) ^ n * x ^ (2 * n + 1) / (2 * n + 1 : ℕ)

@[simp] theorem cast_atanPrefixQ (x : ℚ) (N : ℕ) :
    (atanPrefixQ x N : ℝ) = atanPrefix (x : ℝ) N := by
  unfold atanPrefixQ atanPrefix
  push_cast <;> rfl

private theorem arctan_terms_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n + 1) / (2 * n + 1 : ℕ)) := by
  intro i j hij
  have hp : x ^ (2 * j + 1) ≤ x ^ (2 * i + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hij) 1)
  have hd : (0 : ℝ) < (2 * i + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hdd : ((2 * i + 1 : ℕ) : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hij) 1)
  exact div_le_div₀ (pow_nonneg hx0 _) hp hd hdd

/-- Even-prefix enclosure derived from the library series and decreasing terms.
No alternating remainder or target enclosure is a hypothesis. -/
theorem arctan_two_mul_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    atanPrefix x (2 * k) ≤ Real.arctan x ∧
      Real.arctan x ≤ atanPrefix x (2 * k) +
        x ^ (2 * (2 * k) + 1) / (2 * (2 * k) + 1 : ℕ) := by
  have hxnorm : ‖x‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  have hs := (Real.hasSum_arctan hxnorm).tendsto_sum_nat
  have ht : Tendsto
      (fun N : ℕ => ∑ n ∈ range N, (-1 : ℝ) ^ n *
        (x ^ (2 * n + 1) / (2 * n + 1 : ℕ))) atTop (𝓝 (Real.arctan x)) := by
    simpa only [mul_div_assoc] using hs
  have hm := arctan_terms_antitone hx0 hx1.le
  have hl := hm.alternating_series_le_tendsto ht k
  have hu := hm.tendsto_le_alternating_series ht k
  have he : (-1 : ℝ) ^ (2 * k) = 1 := by simp
  constructor
  · simpa only [atanPrefix, mul_div_assoc] using hl
  · simpa only [atanPrefix, sum_range_succ, he, one_mul, mul_div_assoc] using hu

/-- The requested N = 230 = 2*115 specialization. -/
theorem arctan_230_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    atanPrefix x 230 ≤ Real.arctan x ∧
      Real.arctan x ≤ atanPrefix x 230 + x ^ 461 / 461 := by
  simpa using arctan_two_mul_bounds hx0 hx1 115

def atan5LowerQ : ℚ := atanPrefixQ (1 / 5) 230
def atan5UpperQ : ℚ := atan5LowerQ + (1 / 5 : ℚ) ^ 461 / 461
def atan239LowerQ : ℚ := atanPrefixQ (1 / 239) 230
def atan239UpperQ : ℚ := atan239LowerQ + (1 / 239 : ℚ) ^ 461 / 461

theorem arctan_one_fifth_bounds :
    (atan5LowerQ : ℝ) ≤ Real.arctan (1 / 5) ∧
      Real.arctan (1 / 5) ≤ (atan5UpperQ : ℝ) := by
  simpa [atan5LowerQ, atan5UpperQ] using
    (arctan_230_bounds (x := (1 : ℝ) / 5) (by norm_num) (by norm_num))

theorem arctan_one_239_bounds :
    (atan239LowerQ : ℝ) ≤ Real.arctan (1 / 239) ∧
      Real.arctan (1 / 239) ≤ (atan239UpperQ : ℝ) := by
  simpa [atan239LowerQ, atan239UpperQ] using
    (arctan_230_bounds (x := (1 : ℝ) / 239) (by norm_num) (by norm_num))

def piLowerQ : ℚ := 16 * atan5LowerQ - 4 * atan239UpperQ
def piUpperQ : ℚ := 16 * atan5UpperQ - 4 * atan239LowerQ

/-- Exact Machin rational sums enclose real pi. -/
theorem pi_machin_bounds : (piLowerQ : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piUpperQ : ℝ) := by
  have h5 := arctan_one_fifth_bounds
  have h239 := arctan_one_239_bounds
  have hm : 4 * Real.arctan (1 / 5) - Real.arctan (1 / 239) = Real.pi / 4 := by
    simpa only [one_div] using Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hm' : Real.pi = 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
    calc
      Real.pi = 4 * (Real.pi / 4) := by ring
      _ = 4 * (4 * Real.arctan (1 / 5) - Real.arctan (1 / 239)) := by rw [hm]
      _ = _ := by ring
  unfold piLowerQ piUpperQ
  push_cast
  rw [hm']
  exact ⟨sub_le_sub (mul_le_mul_of_nonneg_left h5.1 (by norm_num))
      (mul_le_mul_of_nonneg_left h239.2 (by norm_num)),
    sub_le_sub (mul_le_mul_of_nonneg_left h5.2 (by norm_num))
      (mul_le_mul_of_nonneg_left h239.1 (by norm_num))⟩

set_option exponentiation.threshold 1024 in
/-- Exact rational width; this is much smaller than 10^-250. -/
theorem pi_machin_width : piUpperQ - piLowerQ < (1 : ℚ) / 10 ^ 320 := by
  have hw : piUpperQ - piLowerQ =
      16 * ((1 / 5 : ℚ) ^ 461 / 461) + 4 * ((1 / 239 : ℚ) ^ 461 / 461) := by
    unfold piUpperQ piLowerQ atan5UpperQ atan239UpperQ
    ring
  rw [hw]
  norm_num

set_option exponentiation.threshold 1024 in
/-- Coarse admissibility of the exact Machin endpoints, independent of the
optional closed-value evaluations and 250-place rounding proofs. -/
private theorem machin_endpoints_range :
    (0 : ℝ) ≤ (piLowerQ : ℝ) ∧ (piUpperQ : ℝ) < 8 := by
  have hpi := pi_machin_bounds
  have hwq : piUpperQ - piLowerQ < (1 : ℚ) :=
    pi_machin_width.trans (by norm_num)
  have hw : (piUpperQ : ℝ) - (piLowerQ : ℝ) < 1 := by exact_mod_cast hwq
  have ha : (piUpperQ : ℝ) < (piLowerQ : ℝ) + 1 := sub_lt_iff_lt_add'.mp hw
  have h3 : (3 : ℝ) < (piLowerQ : ℝ) + 1 :=
    Real.pi_gt_three.trans (hpi.2.trans_lt ha)
  have hl2 : (2 : ℝ) < (piLowerQ : ℝ) := by
    apply (add_lt_add_iff_right (1 : ℝ)).mp
    convert h3 using 1 <;> norm_num
  constructor
  · exact (by norm_num : (0 : ℝ) ≤ 2).trans hl2.le
  · calc
      (piUpperQ : ℝ) < (piLowerQ : ℝ) + 1 := ha
      _ ≤ Real.pi + 1 := by linarith [hpi.1]
      _ < 8 := by linarith [Real.pi_lt_four]

/-- Taylor polynomial through degree N (N+1 terms). -/
def expPrefix (y : ℝ) (N : ℕ) : ℝ := ∑ n ∈ range (N + 1), y ^ n / n.factorial

def expUpper (y : ℝ) (N : ℕ) : ℝ :=
  expPrefix y N + (y ^ (N + 1) / (N + 1).factorial) / (1 - y / (N + 2 : ℕ))

def expPrefixQ (y : ℚ) (N : ℕ) : ℚ := ∑ n ∈ range (N + 1), y ^ n / n.factorial

def expUpperQ (y : ℚ) (N : ℕ) : ℚ :=
  expPrefixQ y N + (y ^ (N + 1) / (N + 1).factorial) / (1 - y / (N + 2 : ℕ))

@[simp] theorem cast_expPrefixQ (y : ℚ) (N : ℕ) :
    (expPrefixQ y N : ℝ) = expPrefix (y : ℝ) N := by
  unfold expPrefixQ expPrefix
  push_cast <;> rfl

@[simp] theorem cast_expUpperQ (y : ℚ) (N : ℕ) :
    (expUpperQ y N : ℝ) = expUpper (y : ℝ) N := by
  simp [expUpperQ, expUpper]

private theorem real_exp_series (y : ℝ) :
    HasSum (fun n : ℕ => y ^ n / n.factorial) (Real.exp y) := by
  simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp y

/-- The actual denominator is positive, including at N = 0 and y = 0. -/
theorem exp_tail_ratio_lt_one {y : ℝ} (hy : y < 1) (N : ℕ) :
    y / (N + 2 : ℕ) < 1 := by
  have hd : (0 : ℝ) < (N + 2 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hd1 : (1 : ℝ) ≤ (N + 2 : ℕ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le (N + 1)))
  exact (div_lt_iff₀ hd).2 (by simpa only [one_mul] using hy.trans_le hd1)

/-- First omitted term times a geometric majorant; factorial growth is proved
by the existing Nat.factorial_mul_pow_le_factorial theorem. -/
private theorem exp_tail_term_le {y : ℝ} (hy0 : 0 ≤ y) (N n : ℕ) :
    y ^ (n + (N + 1)) / (n + (N + 1)).factorial ≤
      (y ^ (N + 1) / (N + 1).factorial) * (y / (N + 2 : ℕ)) ^ n := by
  have hfact : (0 : ℝ) < (N + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hd : (0 : ℝ) < (N + 2 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  calc
    _ = y ^ ((N + 1) + n) / ((N + 1) + n).factorial := by rw [Nat.add_comm n (N + 1)]
    _ ≤ y ^ ((N + 1) + n) /
        ((↑((N + 1).factorial) : ℝ) * ((N + 2 : ℕ) : ℝ) ^ n) := by
      apply div_le_div_of_nonneg_left (pow_nonneg hy0 _) (mul_pos hfact (pow_pos hd n))
      exact_mod_cast (Nat.factorial_mul_pow_le_factorial (m := N + 1) (n := n))
    _ = _ := by
      rw [pow_add, div_pow]
      simp only [div_eq_mul_inv, mul_inv]
      ring

/-- Positive Taylor/geometric-tail enclosure for every N >= 0 and 0 <= y < 1.
The upper remainder is exactly firstOmitted / (1 - y/(N+2)). -/
theorem exp_taylor_geometric_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (N : ℕ) :
    expPrefix y N ≤ Real.exp y ∧ Real.exp y ≤ expUpper y N := by
  have hr := exp_tail_ratio_lt_one hy1 N
  have hden : 0 < 1 - y / (N + 2 : ℕ) := sub_pos.mpr hr
  have hs : HasSum (fun n : ℕ => y ^ (n + (N + 1)) / (n + (N + 1)).factorial)
      (Real.exp y - expPrefix y N) := by
    exact (hasSum_nat_add_iff' (N + 1)).2 (real_exp_series y)
  have hf : ∀ n : ℕ,
      ‖y ^ (n + (N + 1)) / (n + (N + 1)).factorial‖ ≤
        (y ^ (N + 1) / (N + 1).factorial) * (y / (N + 2 : ℕ)) ^ n := by
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (pow_nonneg hy0 _) (Nat.cast_nonneg _))]
    exact exp_tail_term_le hy0 N n
  have hb := norm_sub_le_of_geometric_bound_of_hasSum (sub_pos.mp hden) hf hs 0
  have habs : |Real.exp y - expPrefix y N| ≤
      (y ^ (N + 1) / (N + 1).factorial) / (1 - y / (N + 2 : ℕ)) := by
    simpa only [range_zero, sum_empty, zero_sub, norm_neg, Real.norm_eq_abs,
      pow_zero, mul_one] using hb
  have hl : expPrefix y N ≤ Real.exp y := Real.sum_le_exp_of_nonneg hy0 (N + 1)
  have hrem : 0 ≤ Real.exp y - expPrefix y N := sub_nonneg.mpr hl
  rw [abs_of_nonneg hrem] at habs
  constructor
  · exact hl
  · exact sub_le_iff_le_add'.mp habs

private theorem expPrefix_pos {y : ℝ} (hy0 : 0 ≤ y) (N : ℕ) : 0 < expPrefix y N := by
  have h1 : (1 : ℝ) ≤ expPrefix y N := by
    have h := Finset.single_le_sum (s := range (N + 1))
      (f := fun n : ℕ => y ^ n / (n.factorial : ℝ))
      (fun n _ => div_nonneg (pow_nonneg hy0 n) (Nat.cast_nonneg _))
      (show 0 ∈ range (N + 1) by simp)
    simpa [expPrefix] using h
  exact zero_lt_one.trans_le h1

/-- Exact exp_nat_mul followed by order-reversing reciprocal, with positivity. -/
theorem exp_neg_sixteen_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (N : ℕ) :
    1 / expUpper y N ^ 16 ≤ Real.exp (-(16 * y)) ∧
      Real.exp (-(16 * y)) ≤ 1 / expPrefix y N ^ 16 := by
  have ht := exp_taylor_geometric_bounds hy0 hy1 N
  have hp := expPrefix_pos hy0 N
  have hlo : expPrefix y N ^ 16 ≤ Real.exp y ^ 16 :=
    pow_le_pow_left₀ hp.le ht.1 16
  have hup : Real.exp y ^ 16 ≤ expUpper y N ^ 16 :=
    pow_le_pow_left₀ (Real.exp_pos y).le ht.2 16
  have h : Real.exp (16 * y) = Real.exp y ^ 16 := by
    simpa only [Nat.cast_ofNat] using Real.exp_nat_mul y 16
  have hid : Real.exp (-(16 * y)) = 1 / Real.exp y ^ 16 := by
    rw [Real.exp_neg, h, one_div]
  rw [hid]
  exact ⟨one_div_le_one_div_of_le (pow_pos (Real.exp_pos y) 16) hup,
    one_div_le_one_div_of_le (pow_pos hp 16) hlo⟩

/-- Exact finite rational inputs, through degree 240, evaluated at 12/16. -/
def expNeg12LowerQ : ℚ := 1 / expUpperQ (3 / 4) 240 ^ 16
def expNeg12UpperQ : ℚ := 1 / expPrefixQ (3 / 4) 240 ^ 16

theorem exp_neg_twelve_bounds :
    (expNeg12LowerQ : ℝ) ≤ Real.exp (-12) ∧
      Real.exp (-12) ≤ (expNeg12UpperQ : ℝ) := by
  have h := exp_neg_sixteen_bounds (y := (3 : ℝ) / 4) (by norm_num) (by norm_num) 240
  convert h using 1 <;>
    norm_num [expNeg12LowerQ, expNeg12UpperQ]

/-- These endpoints use the exact Machin rational sums, not an assumed pi bound. -/
def expNegTwoPiLowerQ : ℚ := 1 / expUpperQ (piUpperQ / 8) 240 ^ 16
def expNegTwoPiUpperQ : ℚ := 1 / expPrefixQ (piLowerQ / 8) 240 ^ 16

theorem exp_neg_two_pi_bounds :
    (expNegTwoPiLowerQ : ℝ) ≤ Real.exp (-(2 * Real.pi)) ∧
      Real.exp (-(2 * Real.pi)) ≤ (expNegTwoPiUpperQ : ℝ) := by
  have hpi := pi_machin_bounds
  have hr := machin_endpoints_range
  have hlu : (piLowerQ : ℝ) ≤ (piUpperQ : ℝ) := hpi.1.trans hpi.2
  have hylo0 : 0 ≤ (piLowerQ : ℝ) / 8 := div_nonneg hr.1 (by norm_num)
  have hylo1 : (piLowerQ : ℝ) / 8 < 1 :=
    (div_lt_one (by norm_num : (0 : ℝ) < 8)).mpr (hlu.trans_lt hr.2)
  have hyhi0 : 0 ≤ (piUpperQ : ℝ) / 8 := div_nonneg (hr.1.trans hlu) (by norm_num)
  have hyhi1 : (piUpperQ : ℝ) / 8 < 1 :=
    (div_lt_one (by norm_num : (0 : ℝ) < 8)).mpr hr.2
  have hlo := exp_neg_sixteen_bounds hylo0 hylo1 240
  have hhi := exp_neg_sixteen_bounds hyhi0 hyhi1 240
  have helo : Real.exp (-(16 * ((piUpperQ : ℝ) / 8))) ≤ Real.exp (-(2 * Real.pi)) :=
    Real.exp_le_exp.mpr (by
      convert neg_le_neg (mul_le_mul_of_nonneg_left hpi.2 (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;>
        ring)
  have hehi : Real.exp (-(2 * Real.pi)) ≤ Real.exp (-(16 * ((piLowerQ : ℝ) / 8))) :=
    Real.exp_le_exp.mpr (by
      convert neg_le_neg (mul_le_mul_of_nonneg_left hpi.1 (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;>
        ring)
  constructor
  · simpa [expNegTwoPiLowerQ] using hhi.1.trans helo
  · simpa [expNegTwoPiUpperQ] using hehi.trans hlo.2


end RHFiniteGaussian.AnalyticEndpoints
