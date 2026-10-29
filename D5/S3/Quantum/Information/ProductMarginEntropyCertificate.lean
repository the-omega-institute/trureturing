/- GID: D5/S3/Quantum/Information/ProductMarginEntropyCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ProductMarginEntropyCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A closed-interval binary entropy certificate for product-margin information budgets. -/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Information.ProductMarginEntropyCertificate
open Set

private lemma fifth_log_gap :
    4 * Real.log 2 - 5 * Real.binEntropy (1 / 5) = Real.log (4096 / 3125) := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h4096 : Real.log (4096 / 3125 : ℝ) = 6 * Real.log 4 - 5 * Real.log 5 := by
    rw [show (4096 / 3125 : ℝ) = 4 ^ 6 / 5 ^ 5 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [h4096, h4]
  norm_num [Real.binEntropy, Real.log_div, Real.log_inv]
  rw [h4]
  ring

private lemma ratio_entropy_bound {b : ℝ} (hb : b ∈ Icc 0 (1 / 6)) :
    (1 - b) * Real.binEntropy (b / (1 - b)) ≤ Real.binEntropy b := by
  have hd : 0 < 1 - b := by linarith [hb.2]
  have hq : b / (1 - b) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hb.1 hd.le
    · rw [div_le_one hd]; linarith [hb.2]
  have h := Real.strictConcave_binEntropy.concaveOn.2 hq
    (show (0 : ℝ) ∈ Icc 0 1 by simp) hd.le hb.1 (by ring : 1 - b + b = 1)
  have hid : (1 - b) * (b / (1 - b)) = b := by field_simp
  simpa only [smul_eq_mul, Real.binEntropy_zero, mul_zero, add_zero, hid] using h

/-- The scalar entropy certificate is valid on the entire closed high-reliability interval.
Binary entropy uses natural logarithms and includes its continuous values at zero and one. -/
theorem binary_entropy_certificate {s : ℝ} (hs : s ∈ Icc (2 / 3) 1) :
    (1 - s) / (2 * s) * Real.log (4096 / 3125) ≤
      Real.log 2 - Real.binEntropy ((1 - s) / (1 + s)) -
        (3 - 2 / s) * (Real.log 2 - Real.binEntropy ((1 + s) / 2)) := by
  let b := (1 - s) / 2
  have hb : b ∈ Icc (0 : ℝ) (1 / 6) := by dsimp [b]; constructor <;> linarith [hs.1, hs.2]
  have hs0 : 0 < s := by linarith [hs.1]
  have hd : 0 < 1 - b := by linarith [hb.2]
  have hb5 : b ≤ (1 / 5 : ℝ) := by linarith [hb.2]
  have hH : Real.binEntropy b ≤ Real.binEntropy (1 / 5) :=
    Real.binEntropy_strictMonoOn.monotoneOn ⟨hb.1, by linarith [hb.2]⟩
      (by norm_num : (1 / 5 : ℝ) ∈ Icc 0 2⁻¹) hb5
  have hHb : 0 ≤ Real.binEntropy b := Real.binEntropy_nonneg hb.1 (by linarith [hb.2])
  have hratio := ratio_entropy_bound hb
  have hratio' : Real.binEntropy (b / (1 - b)) ≤ Real.binEntropy b / (1 - b) :=
    (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hratio)
  have hcoef : 0 ≤ (5 - 6 * b) / (1 - b) ∧ (5 - 6 * b) / (1 - b) ≤ 5 := by
    constructor
    · exact div_nonneg (by linarith [hb.2]) hd.le
    · rw [div_le_iff₀ hd]; linarith [hb.1]
  have hbudget : (5 - 6 * b) / (1 - b) * Real.binEntropy b ≤
      5 * Real.binEntropy (1 / 5) := by
    calc
      _ ≤ 5 * Real.binEntropy b := mul_le_mul_of_nonneg_right hcoef.2 hHb
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (by norm_num)
  have hn : b * Real.log (4096 / 3125) ≤
      4 * b * Real.log 2 + (1 - 6 * b) * Real.binEntropy b -
        (1 - 2 * b) * Real.binEntropy (b / (1 - b)) := by
    have hr := mul_le_mul_of_nonneg_left hratio' (show 0 ≤ 1 - 2 * b by linarith [hb.2])
    have he : 4 * b * Real.log 2 + (1 - 6 * b) * Real.binEntropy b -
        (1 - 2 * b) * (Real.binEntropy b / (1 - b)) =
        b * (4 * Real.log 2 - (5 - 6 * b) / (1 - b) * Real.binEntropy b) := by
      field_simp; ring
    have hg := mul_le_mul_of_nonneg_left hbudget hb.1
    calc
      b * Real.log (4096 / 3125) = b * (4 * Real.log 2 - 5 * Real.binEntropy (1 / 5)) := by rw [fifth_log_gap]
      _ ≤ b * (4 * Real.log 2 - (5 - 6 * b) / (1 - b) * Real.binEntropy b) := by nlinarith only [hg]
      _ = _ := he.symm
      _ ≤ _ := by linarith only [hr]
  have hsym : Real.binEntropy ((1 + s) / 2) = Real.binEntropy b := by
    rw [← Real.binEntropy_one_sub ((1 + s) / 2)]
    congr 1; dsimp [b]; ring
  have hq : (1 - s) / (1 + s) = b / (1 - b) := by
    dsimp [b]; field_simp [show 1 + s ≠ 0 by linarith]; ring
  have hn' : b * Real.log (4096 / 3125) ≤ s *
      (Real.log 2 - Real.binEntropy ((1 - s) / (1 + s)) -
        (3 - 2 / s) * (Real.log 2 - Real.binEntropy ((1 + s) / 2))) := by
    rw [hsym, hq]
    convert hn using 1
    dsimp [b]; field_simp; ring
  have hf : b * Real.log (4096 / 3125) / s ≤
      Real.log 2 - Real.binEntropy ((1 - s) / (1 + s)) -
        (3 - 2 / s) * (Real.log 2 - Real.binEntropy ((1 + s) / 2)) :=
    (div_le_iff₀ hs0).mpr (by simpa only [mul_comm] using hn')
  convert hf using 1
  dsimp [b]; field_simp; ring


/-- A sufficient scalar information budget. The quantum application must separately prove
all three information estimates and the trace estimate for its actual density state. -/
theorem information_budget_nonneg {a b k j c d : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hk : 0 ≤ k) (hc : 0 ≤ c) (hd : 0 ≤ d) (hj : 0 ≤ j)
    (hkj : k ≤ (1 - Real.sqrt (a * b)) / (1 + Real.sqrt (a * b)))
    (hjc : j ≤ b * c) (hjd : j ≤ a * d)
    (hja : j ≤ Real.log 2 - Real.binEntropy ((1 + Real.sqrt (a * b)) / 2)) :
    0 ≤ Real.log 2 - Real.binEntropy k + c + d - 3 * j := by
  have hh : 0 ≤ Real.log 2 - Real.binEntropy k := sub_nonneg.mpr Real.binEntropy_le_log_two
  by_cases ha0 : a = 0
  · simp only [ha0, zero_mul] at hjd
    have hj0 : j = 0 := le_antisymm hjd hj
    rw [hj0]; linarith
  by_cases hb0 : b = 0
  · simp only [hb0, zero_mul] at hjc
    have hj0 : j = 0 := le_antisymm hjc hj
    rw [hj0]; linarith
  have ha' : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
  let s := Real.sqrt (a * b)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos ha' hb')
  have hs2 : s ^ 2 = a * b := Real.sq_sqrt (mul_pos ha' hb').le
  have hs1 : s ≤ 1 := by
    have hab : a * b ≤ 1 := mul_le_one₀ ha.2 hb.1 hb.2
    nlinarith [hs.le]
  have hcj : j / b ≤ c := (div_le_iff₀ hb').mpr (by simpa only [mul_comm] using hjc)
  have hdj : j / a ≤ d := (div_le_iff₀ ha').mpr (by simpa only [mul_comm] using hjd)
  have hsum : (1 / a + 1 / b) * j ≤ c + d := by
    simp only [div_eq_mul_inv] at hcj hdj ⊢
    nlinarith only [hcj, hdj]
  by_cases hlow : 3 ≤ 1 / a + 1 / b
  · have hmul := mul_le_mul_of_nonneg_right hlow hj
    linarith
  have ham : 2 * s ≤ a + b := by nlinarith [sq_nonneg (a - b)]
  have hinv : 2 / s ≤ 1 / a + 1 / b := by
    calc
      2 / s ≤ (a + b) / (a * b) := by
        apply (div_le_div_iff₀ hs (mul_pos ha' hb')).mpr
        nlinarith [mul_nonneg hs.le (sub_nonneg.mpr ham)]
      _ = _ := by field_simp; ring
  have hhigh : 2 / 3 ≤ s := by
    have he : 2 / s < 3 := lt_of_le_of_lt hinv (lt_of_not_ge hlow)
    have he' := (div_lt_iff₀ hs).mp he
    linarith
  have hq0 : 0 ≤ (1 - s) / (1 + s) := div_nonneg (sub_nonneg.mpr hs1) (by positivity)
  have hq5 : (1 - s) / (1 + s) ≤ (1 / 5 : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < 1 + s)]
    linarith
  have hH : Real.binEntropy k ≤ Real.binEntropy ((1 - s) / (1 + s)) :=
    Real.binEntropy_strictMonoOn.monotoneOn ⟨hk, by linarith [hkj]⟩
      ⟨hq0, by norm_num; linarith⟩ hkj
  have hL : 0 ≤ Real.log 2 - Real.binEntropy ((1 + s) / 2) :=
    sub_nonneg.mpr Real.binEntropy_le_log_two
  have hcoef : 0 ≤ 3 - 2 / s := by linarith
  have hinfo : (3 - (1 / a + 1 / b)) * j ≤
      (3 - 2 / s) * (Real.log 2 - Real.binEntropy ((1 + s) / 2)) := by
    calc
      _ ≤ (3 - 2 / s) * j := mul_le_mul_of_nonneg_right (by linarith) hj
      _ ≤ _ := mul_le_mul_of_nonneg_left hja hcoef
  have hcert := binary_entropy_certificate ⟨hhigh, hs1⟩
  have hpositive : 0 ≤ (1 - s) / (2 * s) * Real.log (4096 / 3125) :=
    mul_nonneg (div_nonneg (by linarith) (by positivity)) (Real.log_pos (by norm_num)).le
  dsimp only [s] at hcert hpositive hinfo hH
  nlinarith only [hsum, hinfo, hcert, hpositive, hH]

#print axioms information_budget_nonneg

#print axioms binary_entropy_certificate
end D5.S3.Quantum.Information.ProductMarginEntropyCertificate
