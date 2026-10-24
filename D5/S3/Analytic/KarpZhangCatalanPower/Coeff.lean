/- GID: D5/S3/Analytic/KarpZhangCatalanPower/Coeff
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangCatalanPower/Coeff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Polynomial]
   utility: none
   digest: Polynomial form and strict total positivity of the Catalan power coefficients. -/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
The coefficients in formula (15) of Karp--Zhang, arXiv:2305.09029.
Search-before-prove covered D5 and pinned Mathlib for Vandermonde,
`Ring.descPochhammer_smeval_add`, `ascPochhammer_eval_add`, Catalan,
Hagen, Rothe and Lagrange. The Pochhammer multiplication and positivity
lemmas are reused here; the Catalan Lagrange bridge is used in Index.

The quotient is literal, so its polynomial identity is stated away from
the denominator zeros. In particular, all nonnegative parameters are covered.
admission_basis: escape-witness; witness: tp2.
utility none: the statements quantify over arbitrary degrees and real parameters;
none is a finite numerical certificate, enumerator, checker or numeric reduction.
-/

noncomputable section
open Polynomial Finset

namespace D5.S3.Analytic.KarpZhangCatalanPower.Coeff

/-- The literal rising-factorial quotient in formula (15). -/
def a (n : ℕ) (t : ℝ) : ℝ :=
  (ascPochhammer ℝ (2 * n)).eval t /
    ((ascPochhammer ℝ n).eval (t + 1) * (n.factorial : ℝ))

/-- The polynomial continuation of the coefficient. -/
def coeffPoly : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C ((n + 1).factorial : ℝ)⁻¹ * X *
      (ascPochhammer ℝ n).comp (X + C (n + 2 : ℝ))

/- proof_shape: bind-only; escape_witness: none;
consumer: a_eq_polynomial, a_pos, adjacent_ratio. -/
lemma coeffPoly_succ_eval (n : ℕ) (t : ℝ) :
    (coeffPoly (n + 1)).eval t =
      t * (ascPochhammer ℝ n).eval (t + n + 2) / ((n + 1).factorial : ℝ) := by
  simp only [coeffPoly, eval_mul, eval_C, eval_X, eval_comp, eval_add]
  ring

/- proof_shape: bind-only; escape_witness: none;
consumer: a_eq_polynomial. -/
private lemma poch_split (n : ℕ) (t : ℝ) :
    (ascPochhammer ℝ (2 * (n + 1))).eval t =
      t * (ascPochhammer ℝ (n + 1)).eval (t + 1) *
        (ascPochhammer ℝ n).eval (t + n + 2) := by
  rw [show 2 * (n + 1) = (n + 1 + n) + 1 by omega,
    ascPochhammer_succ_left]
  simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
  have h := congrArg (fun p : ℝ[X] => p.eval (t + 1))
    (ascPochhammer_mul ℝ (n + 1) n)
  simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at h
  rw [← h]
  push_cast
  ring

/- proof_shape: bind-only; escape_witness: none;
consumer: a_pos, a_nonneg, adjacent_ratio, Index.index_law. -/
lemma a_eq_polynomial (n : ℕ) {t : ℝ} (ht : -1 < t) :
    a n t = (coeffPoly n).eval t := by
  cases n with
  | zero => simp [a, coeffPoly]
  | succ n =>
    rw [a, poch_split, coeffPoly_succ_eval]
    have hp := (ascPochhammer_pos (n + 1) (t + 1) (by linarith)).ne'
    have hf : ((n + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp

/- proof_shape: bind-only; escape_witness: none;
consumer: a_product. -/
private lemma poch_prod (n : ℕ) (t : ℝ) :
    (ascPochhammer ℝ n).eval t = ∏ j ∈ range n, (t + j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ih, prod_range_succ]

/- proof_shape: bind-only; escape_witness: none;
consumer: a_pos. -/
theorem a_product {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : -1 < t) :
    a n t = t / (n.factorial : ℝ) * ∏ r ∈ Ico (n + 1) (2 * n), (t + r) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one]
  rw [a_eq_polynomial _ ht, coeffPoly_succ_eval, poch_prod, prod_Ico_eq_prod_range]
  rw [show 2 * (n + 1) - (n + 1 + 1) = n by omega]
  simp_rw [Nat.cast_add, Nat.cast_one]
  have h : (∏ j ∈ range n, (t + (n : ℝ) + 2 + j)) =
      ∏ j ∈ range n, (t + (n + 1 + 1 + j)) := by
    apply prod_congr rfl
    intro j hj
    ring
  rw [h]
  ring

/- proof_shape: bind-only; escape_witness: none;
consumer: tp2, Index.hasDerivAt_a, Interval.tail_nonneg. -/
lemma a_pos (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 < a n t := by
  cases n with
  | zero => norm_num [a]
  | succ n =>
    rw [a_product (by omega) (by linarith)]
    exact mul_pos (div_pos ht (by positivity)) (prod_pos (fun r hr => by positivity))

/- proof_shape: bind-only; escape_witness: none;
consumer: a_nonneg, Interval.tail_nonneg. -/
lemma a_zero_parameter {n : ℕ} (hn : 0 < n) : a n 0 = 0 := by
  simp [a, ascPochhammer_ne_zero_eval_zero ℝ (by omega : 2 * n ≠ 0)]

/- proof_shape: bind-only; escape_witness: none;
consumer: Index.index_law, Interval.tail_nonneg. -/
lemma a_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ a n t := by
  rcases ht.eq_or_lt with rfl | ht
  · cases n with
    | zero => norm_num [a]
    | succ n => rw [a_zero_parameter (by omega)]
  · exact (a_pos n ht).le

/- proof_shape: bind-only; escape_witness: none;
consumer: adjacent_tp2. -/
lemma adjacent_ratio (n : ℕ) {t : ℝ} (ht : 0 < t) :
    a (n + 1) t = a n t *
      ((t + 2 * n) * (t + 2 * n + 1) / ((t + n + 1) * (n + 1))) := by
  have hp := (ascPochhammer_pos n (t + 1) (by linarith)).ne'
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have htn : t + n + 1 ≠ 0 := by positivity
  simp only [a, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  push_cast
  field_simp
  <;> ring

/- proof_shape: bind-only; escape_witness: none;
consumer: tp2. -/
private lemma adjacent_tp2 (n : ℕ) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    a (n + 1) u * a n v < a n u * a (n + 1) v := by
  have hv : 0 < v := hu.trans huv
  rw [adjacent_ratio n hu, adjacent_ratio n hv]
  have hratio :
      (u + 2 * n) * (u + 2 * n + 1) / ((u + n + 1) * (n + 1)) <
        (v + 2 * n) * (v + 2 * n + 1) / ((v + n + 1) * (n + 1)) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hcross :
        (v + 2 * n) * (v + 2 * n + 1) * ((u + n + 1) * (n + 1)) -
          (u + 2 * n) * (u + 2 * n + 1) * ((v + n + 1) * (n + 1)) =
        (v - u) * (n + 1) *
          (u * v + (n + 1) * (u + v) + 3 * n + 1) := by ring
    have hp : 0 < (v - u) * (n + 1) *
        (u * v + (n + 1) * (u + v) + 3 * n + 1) := by positivity
    linarith
  have h := mul_lt_mul_of_pos_left hratio (mul_pos (a_pos n hu) (a_pos n hv))
  nlinarith only [h]

/- proof_shape: content; escape_witness: tp2 (induction propagates the
adjacent cross-product order through arbitrary degree gaps);
consumer: tp2_le, Interval.slice_derivative_pos. -/
theorem tp2 {u v : ℝ} (hu : 0 < u) (huv : u < v) {i l : ℕ} (hil : i < l) :
    a l u * a i v < a i u * a l v := by
  have hv : 0 < v := hu.trans huv
  induction l with
  | zero => omega
  | succ l ih =>
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hil) with rfl | hil'
    · exact adjacent_tp2 _ hu huv
    · have h₁ := ih hil'
      have h₂ := adjacent_tp2 l hu huv
      have hl : 0 < a l u := a_pos l hu
      have hlv : 0 < a l v := a_pos l hv
      have hi : 0 < a i u := a_pos i hu
      have hdiv₁ : a i v / a i u < a l v / a l u :=
        (div_lt_div_iff₀ hi hl).mpr (by nlinarith only [h₁])
      have hdiv₂ : a l v / a l u < a (l + 1) v / a (l + 1) u :=
        (div_lt_div_iff₀ hl (a_pos (l + 1) hu)).mpr (by nlinarith only [h₂])
      have h := (div_lt_div_iff₀ hi (a_pos (l + 1) hu)).mp (hdiv₁.trans hdiv₂)
      nlinarith only [h]

/- proof_shape: content; escape_witness: tp2;
consumer: Interval.slice_derivative_nonneg. -/
theorem tp2_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) {i l : ℕ} (hil : i < l) :
    a l u * a i v ≤ a i u * a l v := by
  rcases huv.eq_or_lt with rfl | h
  · exact le_of_eq (mul_comm _ _)
  · exact (tp2 hu h hil).le

end D5.S3.Analytic.KarpZhangCatalanPower.Coeff
