/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/OneZeroMatching
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative entropy control of the centering loss in a singular four-cycle. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TwoNodeDeficit
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Matching the opposite endpoints of a four-cycle with a zero spectral node. -/

namespace RefinedBMV.Tracial

noncomputable section

private def completeTwo (a c : ℝ) : ℕ → ℝ
  | 0 => 1
  | p + 1 => c * completeTwo a c p + a ^ (p + 1)

private def completeThree (a c b : ℝ) : ℕ → ℝ
  | 0 => 1
  | p + 1 => b * completeThree a c b p + completeTwo a c (p + 1)

private def completeDouble (a c b : ℝ) : ℕ → ℝ
  | 0 => 1
  | p + 1 => b * completeDouble a c b p + completeThree a c b (p + 1)


private theorem completeTwo_eq_sum (a c : ℝ) (p : ℕ) :
    completeTwo a c p = ∑ j ∈ Finset.range (p + 1), c ^ j * a ^ (p - j) := by
  induction p with
  | zero => simp [completeTwo]
  | succ p ih =>
    rw [completeTwo, ih, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Nat.succ_sub_succ_eq_sub, pow_succ' c, mul_assoc]

private theorem completeThree_eq_sum (a c b : ℝ) (p : ℕ) :
    completeThree a c b p =
      ∑ k ∈ Finset.range (p + 1), b ^ k * completeTwo a c (p - k) := by
  induction p with
  | zero => simp [completeThree, completeTwo]
  | succ p ih =>
    rw [completeThree, ih, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Nat.succ_sub_succ_eq_sub, pow_succ' b, mul_assoc]

private theorem completeDouble_eq_nested_sum (a c b : ℝ) (p : ℕ) :
    completeDouble a c b p =
      ∑ j ∈ Finset.range (p + 1), b ^ j * completeThree a c b (p - j) := by
  induction p with
  | zero => simp [completeDouble, completeThree]
  | succ p ih =>
    rw [completeDouble, ih, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Nat.succ_sub_succ_eq_sub, pow_succ' b, mul_assoc]

private theorem completeDouble_eq_sum (a c b : ℝ) (p : ℕ) :
    completeDouble a c b p =
      ∑ k ∈ Finset.range (p + 1), ((k : ℝ) + 1) * b ^ k * completeTwo a c (p - k) := by
  induction p with
  | zero => simp [completeDouble, completeTwo]
  | succ p ih =>
    have hthree : completeThree a c b (p + 1) =
        (∑ k ∈ Finset.range (p + 1), b ^ (k + 1) * completeTwo a c (p - k)) +
          completeTwo a c (p + 1) := by
      rw [completeThree_eq_sum, Finset.sum_range_succ']
      simp only [pow_zero, one_mul, Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
    rw [completeDouble, ih, hthree, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_add, pow_zero, mul_one, one_mul, Nat.sub_zero,
      Nat.succ_sub_succ_eq_sub]
    rw [← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Nat.cast_succ, pow_succ b k]
    ring

private theorem completeTwo_mul_sub (a c : ℝ) (p : ℕ) :
    (a - c) * completeTwo a c p = a ^ (p + 1) - c ^ (p + 1) := by
  induction p with
  | zero => simp [completeTwo]
  | succ p ih =>
    rw [completeTwo, pow_succ' a (p + 1), pow_succ' c (p + 1)]
    linear_combination c * ih

private theorem completeTwo_diag (a : ℝ) (p : ℕ) :
    completeTwo a a p = ((p : ℝ) + 1) * a ^ p := by
  induction p with
  | zero => simp [completeTwo]
  | succ p ih =>
    rw [completeTwo, ih, Nat.cast_succ, pow_succ a p]
    ring

private theorem completeThree_mul_sub (a c b : ℝ) (p : ℕ) :
    (a - b) * (c - b) * (a - c) * completeThree a c b p =
      a ^ (p + 2) * (c - b) + b ^ (p + 2) * (a - c) - c ^ (p + 2) * (a - b) := by
  induction p with
  | zero => simp [completeThree]; ring
  | succ p ih =>
    rw [completeThree, show p + 1 + 2 = p + 2 + 1 by omega,
      pow_succ' a (p + 2), pow_succ' b (p + 2), pow_succ' c (p + 2)]
    linear_combination b * ih + (a - b) * (c - b) * completeTwo_mul_sub a c (p + 1)

private theorem completeThree_diag_mul_sub (a b : ℝ) (p : ℕ) :
    (a - b) ^ 2 * completeThree a a b p =
      (((p : ℝ) + 1) * (a - b) - b) * a ^ (p + 1) + b ^ (p + 2) := by
  induction p with
  | zero => simp [completeThree]; ring
  | succ p ih =>
    rw [completeThree, completeTwo_diag, Nat.cast_succ,
      show p + 1 + 2 = p + 2 + 1 by omega, pow_succ' b (p + 2),
      pow_succ' a (p + 1)]
    linear_combination b * ih

private theorem completeDouble_mul_sub (a c b : ℝ) (p : ℕ) :
    (a - b) ^ 2 * (c - b) ^ 2 * (a - c) * completeDouble a c b p =
      a ^ (p + 3) * (c - b) ^ 2 - c ^ (p + 3) * (a - b) ^ 2 +
        ((p : ℝ) + 3) * b ^ (p + 2) * (a - b) * (c - b) * (a - c) +
        b ^ (p + 3) * (a + c - 2 * b) * (a - c) := by
  induction p with
  | zero => simp [completeDouble]; ring
  | succ p ih =>
    rw [completeDouble, Nat.cast_succ,
      show p + 1 + 2 = p + 2 + 1 by omega, pow_succ' b (p + 2),
      show p + 1 + 3 = p + 3 + 1 by omega, pow_succ' a (p + 3),
      pow_succ' c (p + 3), pow_succ' b (p + 3)]
    linear_combination b * ih +
      (a - b) * (c - b) * completeThree_mul_sub a c b (p + 1)



private def reciprocalNumerator (a c b : ℝ) (p : ℕ) : ℝ :=
  let r := a - b
  let s := c - b
  let u := a ^ (p + 1)
  let v := b ^ (p + 1)
  let w := c ^ (p + 1)
  b * v * u * r ^ 2 - b * v * w * s ^ 2 +
    ((p : ℝ) + 1) * u * w * r * s * (a - c) -
    b * u * w * (r + s) * (a - c)

private theorem completeDouble_reciprocal_mul_sub {a c b : ℝ} (p : ℕ)
    (ha : a ≠ 0) (hc : c ≠ 0) (hb : b ≠ 0) :
    ((a - b) ^ 2 * (c - b) ^ 2 * (a - c)) *
        ((a * b * c) ^ p * completeDouble a⁻¹ c⁻¹ b⁻¹ p) =
      reciprocalNumerator a c b p := by
  have hab : a⁻¹ - b⁻¹ = -(a - b) / (a * b) := by field_simp; ring
  have hcb : c⁻¹ - b⁻¹ = -(c - b) / (c * b) := by field_simp; ring
  have hac : a⁻¹ - c⁻¹ = -(a - c) / (a * c) := by field_simp; ring
  have hsum : a⁻¹ + c⁻¹ - 2 * b⁻¹ = (-(a - b) * c - (c - b) * a) / (a * b * c) := by
    field_simp
    ring
  have h := completeDouble_mul_sub a⁻¹ c⁻¹ b⁻¹ p
  rw [hab, hcb, hac, hsum] at h
  simp only [inv_pow, pow_add _ p, mul_pow] at h ⊢
  unfold reciprocalNumerator
  simp only [pow_add _ p, pow_one]
  field_simp [ha, hb, hc] at h
  simp only [one_div] at h
  linear_combination -h


private theorem completeHomogeneous_one_zero_surplus_of_distinct {a c b : ℝ} (p : ℕ)
    (ha : a ≠ 0) (hc : c ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c) :
    completeThree a a b p * completeThree c c b p +
      completeDouble a c b p * completeTwo a c p - (completeThree a c b p) ^ 2 =
      ((p : ℝ) + 1) * ((a * b * c) ^ p * completeDouble a⁻¹ c⁻¹ b⁻¹ p) := by
  have hscale : (a - b) ^ 2 * (c - b) ^ 2 * (a - c) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hab))
      (pow_ne_zero _ (sub_ne_zero.mpr hcb))) (pow_ne_zero _ (sub_ne_zero.mpr hac))
  apply mul_left_cancel₀ hscale
  calc
    _ = ((a - b) ^ 2 * completeThree a a b p) *
        ((c - b) ^ 2 * completeThree c c b p) * (a - c) ^ 2 +
        ((a - b) ^ 2 * (c - b) ^ 2 * (a - c) * completeDouble a c b p) *
          ((a - c) * completeTwo a c p) -
        ((a - b) * (c - b) * (a - c) * completeThree a c b p) ^ 2 := by ring
    _ = ((p : ℝ) + 1) * (a - c) * reciprocalNumerator a c b p := by
      rw [completeThree_diag_mul_sub, completeThree_diag_mul_sub, completeDouble_mul_sub,
        completeTwo_mul_sub, completeThree_mul_sub, reciprocalNumerator]
      simp only [show p + 3 = (p + 1) + 2 by omega, show p + 2 = (p + 1) + 1 by omega,
        pow_add _ (p + 1), pow_one]
      ring
    _ = _ := by rw [← completeDouble_reciprocal_mul_sub p ha hc hb]; ring


open FourCopyGap
open private monomial balanced sum_gaps_nested
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

private def completeFour (p : ℕ) (a b c d : ℝ) : ℝ :=
  ∑ g ∈ gaps p, monomial a b c d g

private theorem completeFour_zero (p : ℕ) (a c b : ℝ) :
    completeFour p b c 0 a = completeThree a c b p := by
  rw [completeFour, sum_gaps_nested, completeThree_eq_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [completeTwo_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.sum_eq_single 0]
  · simp [monomial, mul_assoc]
  · intro l hl hne
    simp [monomial, zero_pow hne]
  · simp

private theorem completeThree_zero (p : ℕ) (a c : ℝ) :
    completeThree a c 0 p = completeTwo a c p := by
  rw [completeThree_eq_sum, Finset.sum_eq_single 0]
  · simp
  · intro k hk hne
    simp [zero_pow hne]
  · simp

private theorem completeFour_double (p : ℕ) (a c b : ℝ) :
    completeFour p b b c a = completeDouble a c b p := by
  rw [completeFour, sum_gaps_nested, completeDouble_eq_nested_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [completeThree_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [completeTwo_eq_sum, ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  simp [monomial, mul_assoc]

private theorem gapDefect_zero (p : ℕ) (hp : 0 < p) (a c b : ℝ) :
    gapDefect p b c 0 a = completeThree a c b p := by
  have hpow : (0 : ℝ) ^ ((p : ℝ) / 4) = 0 := Real.zero_rpow (by positivity)
  unfold gapDefect
  simp only [balanced, hpow, mul_zero, zero_mul, sub_zero]
  exact completeFour_zero p a c b


private theorem completeTwo_recurrence {a c : ℝ} (hac : a * c = 1) (n : ℕ) :
    completeTwo a c (n + 2) =
      (a + c) * completeTwo a c (n + 1) - completeTwo a c n := by
  simp only [completeTwo, pow_succ a (n + 1)]
  linear_combination -completeTwo a c n * hac

private theorem completeTwo_card_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a * c = 1)
    (n : ℕ) : (n : ℝ) + 1 ≤ completeTwo a c n := by
  have hsum : 2 ≤ a + c := by
    have hsq : 4 ≤ (a + c) ^ 2 := by nlinarith only [hac, sq_nonneg (a - c)]
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (by norm_num; exact hsq)
  have h (n : ℕ) : (n : ℝ) + 1 ≤ completeTwo a c n ∧
      1 ≤ completeTwo a c (n + 1) - completeTwo a c n := by
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_add, completeTwo, pow_one, mul_one, le_refl, true_and]
      linarith only [hsum]
    | succ n ih =>
      have hn : (n : ℝ) + 2 ≤ completeTwo a c (n + 1) := by linarith only [ih.1, ih.2]
      rw [Nat.cast_succ, show n + 1 + 1 = n + 2 by rfl, completeTwo_recurrence hac]
      have hn0 : 0 ≤ completeTwo a c (n + 1) := (by positivity : 0 ≤ (n : ℝ) + 2).trans hn
      have hextra := mul_nonneg (show 0 ≤ a + c - 2 by linarith) hn0
      constructor <;> nlinarith only [hn, ih.2, hextra]
  exact (h n).1

private theorem completeDouble_sub_one_dom {a c b : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 ≤ b) (hac : a * c = 1) (p : ℕ) :
    completeTwo a c p - ((p : ℝ) + 1) ≤
      completeDouble a c b p - completeDouble 1 1 b p := by
  have hdiff (n : ℕ) : 0 ≤ completeTwo a c n - completeTwo 1 1 n := by
    rw [completeTwo_diag, one_pow, mul_one]
    exact sub_nonneg.mpr (completeTwo_card_le ha hc hac n)
  have hthree (n : ℕ) :
      completeTwo a c n - completeTwo 1 1 n ≤
        completeThree a c b n - completeThree 1 1 b n := by
    simp only [completeThree_eq_sum, ← Finset.sum_sub_distrib, ← mul_sub]
    have h := Finset.single_le_sum
      (f := fun k ↦ b ^ k * (completeTwo a c (n - k) - completeTwo 1 1 (n - k)))
      (fun k _ ↦ mul_nonneg (pow_nonneg hb k) (hdiff (n - k)))
      (Finset.mem_range.mpr (Nat.zero_lt_succ n))
    simpa only [Nat.sub_zero, pow_zero, one_mul] using h
  have hfour :
      completeThree a c b p - completeThree 1 1 b p ≤
        completeDouble a c b p - completeDouble 1 1 b p := by
    simp only [completeDouble_eq_nested_sum, ← Finset.sum_sub_distrib, ← mul_sub]
    have h := Finset.single_le_sum
      (f := fun k ↦ b ^ k * (completeThree a c b (p - k) - completeThree 1 1 b (p - k)))
      (fun k _ ↦ mul_nonneg (pow_nonneg hb k) ((hdiff (p - k)).trans (hthree (p - k))))
      (Finset.mem_range.mpr (Nat.zero_lt_succ p))
    simpa only [Nat.sub_zero, pow_zero, one_mul] using h
  have h := (hthree p).trans hfour
  simpa only [completeTwo_diag, one_pow, mul_one] using h

/-- Exact reciprocal surplus for opposite-endpoint allocation at a zero
spectral node. The one nonzero balanced term is restored before taking
the surplus, so the identity retains the centering loss explicitly. -/
theorem gapDefect_one_zero_reciprocal_surplus (p : ℕ) (hp : 0 < p) {a c b : ℝ}
    (ha : a ≠ 0) (hc : c ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c) :
    gapDefect p b a 0 a * gapDefect p b c 0 c +
      (gapDefect p b b c a + (gaps p).card * balanced p b b c a) * gapDefect p 0 c 0 a -
      (gapDefect p b c 0 a) ^ 2 =
      ((p : ℝ) + 1) * (a * b * c) ^ p *
        (gapDefect p b⁻¹ b⁻¹ c⁻¹ a⁻¹ +
          (gaps p).card * balanced p b⁻¹ b⁻¹ c⁻¹ a⁻¹) := by
  simp only [gapDefect_zero p hp, completeThree_zero]
  have h (x y z : ℝ) :
      gapDefect p z z y x + (gaps p).card * balanced p z z y x = completeDouble x y z p := by
    unfold gapDefect
    rw [sub_add_cancel]
    exact completeFour_double p x y z
  rw [h, h]
  simpa only [mul_assoc] using
    completeHomogeneous_one_zero_surplus_of_distinct p ha hc hb hab hcb hac

private theorem exp_weighted_log_ratio_le_sum {I : Type*} [Fintype I]
    (base tilt energy : I → ℝ) (hbase : ∀ i, 0 < base i) (htilt : ∀ i, 0 < tilt i)
    (htotal : ∑ i, tilt i = 1) :
    Real.exp (∑ i, tilt i * (energy i - Real.log (tilt i / base i))) ≤
      ∑ i, base i * Real.exp (energy i) := by
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := tilt)
    (p := fun i ↦ energy i - Real.log (tilt i / base i))
    (fun i _ ↦ (htilt i).le) htotal (fun _ _ ↦ Set.mem_univ _)
  simpa only [smul_eq_mul] using
    hj.trans_eq (Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_eq_mul, Real.exp_sub, Real.exp_log (div_pos (htilt i) (hbase i))]
      field_simp [(hbase i).ne', (htilt i).ne'])

/-- A centered tilt with bounded relative entropy gives a multiplicative
lower bound on the original exponential moment. -/
theorem exp_neg_le_sum_exp_of_tilt {I : Type*} [Fintype I]
    (base tilt energy : I → ℝ) (hbase : ∀ i, 0 < base i) (htilt : ∀ i, 0 < tilt i)
    (htotal : ∑ i, tilt i = 1) (hcenter : ∑ i, tilt i * energy i = 0) {entropy : ℝ}
    (hentropy : ∑ i, tilt i * Real.log (tilt i / base i) ≤ entropy) :
    Real.exp (-entropy) ≤ ∑ i, base i * Real.exp (energy i) := by
  refine (Real.exp_le_exp.mpr ?_).trans
    (exp_weighted_log_ratio_le_sum base tilt energy hbase htilt htotal)
  simpa only [mul_sub, Finset.sum_sub_distrib, hcenter, zero_sub, neg_le_neg_iff] using hentropy

/-- The surplus of the uncentered products absorbs the part of the centering
loss that is common to both opposite slots. Only its residual enters the
comparison of the centered geometric means. -/
theorem one_zero_matching_of_surplus {z x y w v q v₀ : ℝ}
    (hxy : 0 ≤ x * y) (hcentered : 0 ≤ (w - q) * v)
    (hsurplus : q * v₀ ≤ x * y + w * v - z ^ 2)
    (hresidual : q * (v - v₀) ≤ 2 * Real.sqrt (x * y) * Real.sqrt ((w - q) * v)) :
    z ≤ Real.sqrt (x * y) + Real.sqrt ((w - q) * v) := by
  have hx := Real.sq_sqrt hxy
  have hw := Real.sq_sqrt hcentered
  have hs : z ^ 2 ≤ (Real.sqrt (x * y) + Real.sqrt ((w - q) * v)) ^ 2 := by
    nlinarith only [hx, hw, hsurplus, hresidual]
  exact le_of_pow_le_pow_left₀ two_ne_zero
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hs


private theorem balanced_double_of_mul_one (p : ℕ) {a c b : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : 0 < b) (hac : a * c = 1) :
    balanced p b b c a = b ^ ((p : ℝ) / 2) := by
  have h : c ^ ((p : ℝ) / 4) * a ^ ((p : ℝ) / 4) = 1 := by
    rw [← Real.mul_rpow hc ha, mul_comm c a, hac, Real.one_rpow]
  unfold balanced
  rw [mul_assoc (b ^ ((p : ℝ) / 4) * b ^ ((p : ℝ) / 4)), h, mul_one,
    ← Real.rpow_add hb]
  congr 1
  ring

/-- The finite moment factor that weights the lower two-node degrees. -/
def oneZeroMomentPolynomial (p : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p + 1),
    let j : ℝ := (p - k : ℕ)
    (((k : ℝ) + 1) * (j + 1) * j * (j + 2) /
      (((p : ℝ) + 1) * (p : ℝ) * ((p : ℝ) + 2))) * t ^ k

private theorem oneZeroMomentPolynomial_nonneg (p : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ oneZeroMomentPolynomial p t := by
  unfold oneZeroMomentPolynomial
  exact Finset.sum_nonneg fun k _ ↦ by dsimp; positivity

private theorem completeTwo_sub_card_eq_twoNodeDeficit (n : ℕ) (x : ℝ) :
    completeTwo (Real.exp x) (Real.exp (-x)) n - ((n : ℝ) + 1) = twoNodeDeficit n x := by
  rw [completeTwo_eq_sum, twoNodeDeficit]
  congr 1
  symm
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := by simpa using hk
  rw [Nat.add_sub_cancel, Nat.sub_sub_self hkn, mul_comm]

private theorem completeDouble_sub_one_lower (p : ℕ) (hp : 0 < p) {x b : ℝ}
    (hx : 0 ≤ x) (hb : 0 ≤ b) :
    twoNodeDeficit p x * oneZeroMomentPolynomial p (b / Real.exp x) ≤
      completeDouble (Real.exp x) (Real.exp (-x)) b p - completeDouble 1 1 b p := by
  simp only [completeDouble_eq_sum, ← Finset.sum_sub_distrib, ← mul_sub,
    completeTwo_diag, one_pow, mul_one, completeTwo_sub_card_eq_twoNodeDeficit]
  rw [oneZeroMomentPolynomial, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  have hkn : k ≤ p := by simpa using hk
  have h := twoNodeDeficit_degree_lower (Nat.sub_le p k) hp hx
  have he : Real.exp (-((p : ℝ) - ((p - k : ℕ) : ℝ)) * x) =
      (Real.exp x)⁻¹ ^ k := by
    rw [Nat.cast_sub hkn]
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at h
  dsimp only
  rw [div_pow, div_eq_mul_inv (b ^ k), ← inv_pow]
  calc
    _ = (((k : ℝ) + 1) * b ^ k) *
        (twoNodeDeficit p x *
          ((((p - k : ℕ) : ℝ) + 1) * ((p - k : ℕ) : ℝ) * (((p - k : ℕ) : ℝ) + 2) /
            (((p : ℝ) + 1) * (p : ℝ) * ((p : ℝ) + 2))) * (Real.exp x)⁻¹ ^ k) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

private theorem gapDefect_double_add_balanced (p : ℕ) (a c b : ℝ) :
    gapDefect p b b c a + (gaps p).card * balanced p b b c a = completeDouble a c b p := by
  unfold gapDefect
  rw [sub_add_cancel]
  exact completeFour_double p a c b

/-- Centering the four-slot polynomial with a repeated node retains the
two-node deficit multiplied by the finite moment factor. -/
theorem gapDefect_one_zero_center_lower (p : ℕ) (hp : 0 < p) {x b : ℝ}
    (hx : 0 ≤ x) (hb : 0 < b) :
    twoNodeDeficit p x * oneZeroMomentPolynomial p (b / Real.exp x) ≤
      gapDefect p b b (Real.exp (-x)) (Real.exp x) := by
  have hac : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h₁ := gapDefect_double_add_balanced p (Real.exp x) (Real.exp (-x)) b
  have h₂ := gapDefect_double_add_balanced p 1 1 b
  rw [balanced_double_of_mul_one p (Real.exp_nonneg _) (Real.exp_nonneg _) hb hac] at h₁
  rw [balanced_double_of_mul_one p zero_le_one zero_le_one hb (by norm_num)] at h₂
  have hg := gapDefect_nonneg p hb.le hb.le zero_le_one zero_le_one
  linarith only [h₁, h₂, hg, completeDouble_sub_one_lower p hp hx hb.le]

private theorem gapDefect_normalized_surplus_lower (p : ℕ) (hp : 0 < p) {a c b : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hac : a * c = 1)
    (hab : a ≠ b) (hcb : c ≠ b) (hac' : a ≠ c) :
    ((gaps p).card * b ^ ((p : ℝ) / 2)) * ((p : ℝ) + 1) ≤
      gapDefect p b a 0 a * gapDefect p b c 0 c +
        (gapDefect p b b c a + (gaps p).card * b ^ ((p : ℝ) / 2)) *
          gapDefect p 0 c 0 a - (gapDefect p b c 0 a) ^ 2 := by
  let q : ℝ := (gaps p).card * b ^ ((p : ℝ) / 2)
  have hq : q = (gaps p).card * balanced p b b c a := by
    rw [balanced_double_of_mul_one p ha.le hc.le hb hac]
  have hrecPair : a⁻¹ * c⁻¹ = 1 := by
    rw [← mul_inv, hac, inv_one]
  have hprod : a * b * c = b := by
    calc
      a * b * c = (a * c) * b := by ring
      _ = b := by rw [hac, one_mul]
  have hrec : (a * b * c) ^ p * balanced p b⁻¹ b⁻¹ c⁻¹ a⁻¹ =
      b ^ ((p : ℝ) / 2) := by
    rw [hprod, balanced_double_of_mul_one p (inv_nonneg.mpr ha.le)
      (inv_nonneg.mpr hc.le) (inv_pos.mpr hb) hrecPair, Real.inv_rpow hb.le,
      ← Real.rpow_natCast, ← div_eq_mul_inv, ← Real.rpow_sub hb]
    congr 1
    ring
  have hsurplus := gapDefect_one_zero_reciprocal_surplus p hp
    ha.ne' hc.ne' hb.ne' hab hcb hac'
  rw [← hq] at hsurplus
  have hrecNonneg := gapDefect_nonneg p (inv_nonneg.mpr hb.le) (inv_nonneg.mpr hb.le)
    (inv_nonneg.mpr hc.le) (inv_nonneg.mpr ha.le)
  have hrecTerm :
      0 ≤ ((p : ℝ) + 1) * (a * b * c) ^ p * gapDefect p b⁻¹ b⁻¹ c⁻¹ a⁻¹ :=
    mul_nonneg (by positivity) hrecNonneg
  have hbound :
      q * ((p : ℝ) + 1) ≤
        gapDefect p b a 0 a * gapDefect p b c 0 c +
          (gapDefect p b b c a + q) * gapDefect p 0 c 0 a - (gapDefect p b c 0 a) ^ 2 := by
    rw [hsurplus]
    calc
      _ ≤ ((p : ℝ) + 1) * (a * b * c) ^ p * gapDefect p b⁻¹ b⁻¹ c⁻¹ a⁻¹ +
          q * ((p : ℝ) + 1) := le_add_of_nonneg_left hrecTerm
      _ = _ := by
        rw [show q * ((p : ℝ) + 1) =
          ((p : ℝ) + 1) * (a * b * c) ^ p *
            ((gaps p).card * balanced p b⁻¹ b⁻¹ c⁻¹ a⁻¹) by
          dsimp only [q]
          rw [← hrec]
          ring]
        ring
  exact hbound

/-- A one-zero four-cycle is compensated by its two opposite endpoint pairs
when the sole positive balanced term is at most twice the first matching.
The nonzero sites are normalized by the geometric mean of the opposite pair. -/
theorem gapDefect_one_zero_le_of_balanced_le (p : ℕ) (hp : 0 < p) {a c b : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hac : a * c = 1)
    (hab : a ≠ b) (hcb : c ≠ b) (hac' : a ≠ c)
    (hsmall : (gaps p).card * b ^ ((p : ℝ) / 2) ≤
      2 * Real.sqrt (gapDefect p b a 0 a * gapDefect p b c 0 c)) :
    gapDefect p b c 0 a ≤ Real.sqrt (gapDefect p b a 0 a * gapDefect p b c 0 c) +
      Real.sqrt (gapDefect p b b c a * gapDefect p 0 c 0 a) := by
  let q : ℝ := (gaps p).card * b ^ ((p : ℝ) / 2)
  let d : ℝ := completeTwo a c p - ((p : ℝ) + 1)
  have hq : q = (gaps p).card * balanced p b b c a := by
    rw [balanced_double_of_mul_one p ha.le hc.le hb hac]
  have hq₁ : q = (gaps p).card * balanced p b b 1 1 := by
    rw [balanced_double_of_mul_one p zero_le_one zero_le_one hb (by norm_num)]
  have hV : gapDefect p 0 c 0 a = completeTwo a c p := by
    rw [gapDefect_zero p hp, completeThree_zero]
  have hW (x y : ℝ) :
      gapDefect p b b y x + (gaps p).card * balanced p b b y x = completeDouble x y b p := by
    unfold gapDefect
    rw [sub_add_cancel]
    exact completeFour_double p x y b
  have hdom : d ≤ gapDefect p b b c a := by
    have h₁ := hW a c
    have h₂ := hW 1 1
    rw [← hq] at h₁
    rw [← hq₁] at h₂
    have hg := gapDefect_nonneg p hb.le hb.le zero_le_one zero_le_one
    linarith only [h₁, h₂, hg, completeDouble_sub_one_dom ha hc hb.le hac p]
  have hd : 0 ≤ d := sub_nonneg.mpr (completeTwo_card_le ha hc hac p)
  have hdV : d ≤ gapDefect p 0 c 0 a := by
    rw [hV]
    dsimp only [d]
    have h : 0 ≤ (p : ℝ) + 1 := by positivity
    linarith only [h]
  have hbound := gapDefect_normalized_surplus_lower p hp ha hc hb hac hab hcb hac'
  have hxy : 0 ≤ gapDefect p b a 0 a * gapDefect p b c 0 c :=
    mul_nonneg (gapDefect_nonneg p hb.le ha.le le_rfl ha.le)
      (gapDefect_nonneg p hb.le hc.le le_rfl hc.le)
  have hres : d ≤ Real.sqrt (gapDefect p b b c a * gapDefect p 0 c 0 a) := by
    apply (Real.le_sqrt hd (mul_nonneg (hd.trans hdom) (hd.trans hdV))).mpr
    rw [sq]
    exact mul_le_mul hdom hdV hd (hd.trans hdom)
  have hupper := (mul_le_mul_of_nonneg_right hsmall hd).trans
    (mul_le_mul_of_nonneg_left hres (by positivity))
  have hmatch := one_zero_matching_of_surplus hxy
    (show 0 ≤ (gapDefect p b b c a + q - q) * gapDefect p 0 c 0 a by
      rw [add_sub_cancel_right]
      exact mul_nonneg (hd.trans hdom) (hd.trans hdV))
    hbound (by simpa only [add_sub_cancel_right, hV] using hupper)
  simpa only [add_sub_cancel_right] using hmatch

/-- The normalized moment product pays for the residual centering loss
of a four-cycle with a zero spectral node. -/
theorem gapDefect_one_zero_le_of_moment_product_le (p : ℕ) (hp : 0 < p) {a c b : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hac : a * c = 1)
    (hab : a ≠ b) (hcb : c ≠ b) (hac' : a ≠ c)
    (hmoment : ((gaps p).card * b ^ ((p : ℝ) / 2)) ^ 2 ≤
      4 * (gapDefect p b a 0 a * gapDefect p b c 0 c) * oneZeroMomentPolynomial p (b / a)) :
    gapDefect p b c 0 a ≤ Real.sqrt (gapDefect p b a 0 a * gapDefect p b c 0 c) +
      Real.sqrt (gapDefect p b b c a * gapDefect p 0 c 0 a) := by
  have ha' : 0 < a := zero_lt_one.trans_le ha
  have hcinv : a⁻¹ = c := by
    rw [← one_div, div_eq_iff ha'.ne']
    simpa only [mul_comm] using hac.symm
  have hc : 0 < c := hcinv ▸ inv_pos.mpr ha'
  let q : ℝ := (gaps p).card * b ^ ((p : ℝ) / 2)
  let d : ℝ := completeTwo a c p - ((p : ℝ) + 1)
  let t : ℝ := oneZeroMomentPolynomial p (b / a)
  have hV : gapDefect p 0 c 0 a = completeTwo a c p := by
    rw [gapDefect_zero p hp, completeThree_zero]
  have hdom : d * t ≤ gapDefect p b b c a := by
    have h := gapDefect_one_zero_center_lower p hp (Real.log_nonneg ha) hb
    rw [← completeTwo_sub_card_eq_twoNodeDeficit, Real.exp_neg, Real.exp_log ha', hcinv] at h
    exact h
  have hd : 0 ≤ d := sub_nonneg.mpr (completeTwo_card_le ha' hc hac p)
  have ht : 0 ≤ t := oneZeroMomentPolynomial_nonneg p (div_nonneg hb.le ha'.le)
  have hdV : d ≤ gapDefect p 0 c 0 a := by
    rw [hV]
    dsimp only [d]
    have h : 0 ≤ (p : ℝ) + 1 := by positivity
    linarith only [h]
  let R := gapDefect p b a 0 a * gapDefect p b c 0 c
  let S := gapDefect p b b c a * gapDefect p 0 c 0 a
  have hR : 0 ≤ R :=
    mul_nonneg (gapDefect_nonneg p hb.le ha'.le le_rfl ha'.le)
      (gapDefect_nonneg p hb.le hc.le le_rfl hc.le)
  have hS : 0 ≤ S := mul_nonneg ((mul_nonneg hd ht).trans hdom) (hd.trans hdV)
  have hmoment' : q ^ 2 ≤ 4 * R * t := hmoment
  have hres : q * d ≤ 2 * Real.sqrt R * Real.sqrt S := by
    apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
    calc
      (q * d) ^ 2 = q ^ 2 * d ^ 2 := by ring
      _ ≤ (4 * R * t) * d ^ 2 := mul_le_mul_of_nonneg_right hmoment' (sq_nonneg d)
      _ = (4 * R) * ((d * t) * d) := by ring
      _ ≤ (4 * R) * S := mul_le_mul_of_nonneg_left
        (mul_le_mul hdom hdV hd ((mul_nonneg hd ht).trans hdom)) (by positivity)
      _ = (2 * Real.sqrt R * Real.sqrt S) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hR, Real.sq_sqrt hS]
        ring
  have hupper : q * (gapDefect p 0 c 0 a - ((p : ℝ) + 1)) ≤
      2 * Real.sqrt R * Real.sqrt S := by
    rwa [hV]
  have hbound := gapDefect_normalized_surplus_lower p hp ha' hc hb hac hab hcb hac'
  have hmatch := one_zero_matching_of_surplus hR
    (show 0 ≤ (gapDefect p b b c a + q - q) * gapDefect p 0 c 0 a by
      simpa only [add_sub_cancel_right] using hS)
    hbound (by simpa only [add_sub_cancel_right] using hupper)
  simpa only [add_sub_cancel_right] using hmatch

/-- The first degree satisfies the normalized matching bound directly
from the arithmetic and geometric means of the opposite nodes. -/
theorem gapDefect_one_zero_le_at_one {a c b : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hac : a * c = 1)
    (hab : a ≠ b) (hcb : c ≠ b) (hac' : a ≠ c) :
    gapDefect 1 b c 0 a ≤ Real.sqrt (gapDefect 1 b a 0 a * gapDefect 1 b c 0 c) +
      Real.sqrt (gapDefect 1 b b c a * gapDefect 1 0 c 0 a) := by
  apply gapDefect_one_zero_le_of_balanced_le 1 (by decide) ha hc hb hac hab hcb hac'
  have hside (x : ℝ) : gapDefect 1 b x 0 x = 2 * x + b := by
    rw [gapDefect_zero 1 (by decide)]
    norm_num [completeThree, completeTwo]
    ring
  rw [gaps_card, hside, hside]
  norm_num
  have hs : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hprod : 4 * b ≤ (2 * a + b) * (2 * c + b) := by
    have hsum : 2 ≤ a + c := by
      have hsq : 4 ≤ (a + c) ^ 2 := by nlinarith only [hac, sq_nonneg (a - c)]
      exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (by norm_num; exact hsq)
    nlinarith only [hac, sq_nonneg b, mul_nonneg (sub_nonneg.mpr hsum) hb.le]
  have hroot := Real.sq_sqrt (show 0 ≤ (2 * a + b) * (2 * c + b) by positivity)
  rw [← Real.sqrt_eq_rpow]
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  nlinarith only [hs, hroot, hprod]

#print axioms gapDefect_one_zero_reciprocal_surplus
#print axioms exp_neg_le_sum_exp_of_tilt
#print axioms one_zero_matching_of_surplus
#print axioms gapDefect_one_zero_le_of_balanced_le
#print axioms gapDefect_one_zero_center_lower
#print axioms gapDefect_one_zero_le_of_moment_product_le
#print axioms gapDefect_one_zero_le_at_one

end

end RefinedBMV.Tracial
