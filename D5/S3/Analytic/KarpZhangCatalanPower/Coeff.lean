/- GID: D5/S3/Analytic/KarpZhangCatalanPower/Coeff
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangCatalanPower/Coeff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer, D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge, mathlib/module/Mathlib.Algebra.Polynomial.Roots, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Polynomial]
   utility: none
   digest: Catalan coefficient polynomials, convolution, positive derivative generator and strict total positivity. -/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic
import D5.S3.Combinatorics.Nonnesting.CatalanLagrangeBridge
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
The coefficients in formula (15) of Karp--Zhang, arXiv:2305.09029.
Search-before-prove covered D5 and pinned Mathlib for Vandermonde,
`Ring.descPochhammer_smeval_add`, `ascPochhammer_eval_add`, Catalan,
Hagen, Rothe and Lagrange. The Pochhammer multiplication and positivity
lemmas and the existing Catalan Lagrange substitution transform are reused.
Polynomial uniqueness extends the natural-power convolution to real parameters.
External lookup is disabled for this seat.

The quotient is literal, so its polynomial identity is stated away from
the denominator zeros. In particular, all nonnegative parameters are covered.
admission_basis: escape-witness; witness: tp2.
utility none: the statements quantify over arbitrary degrees and real parameters;
none is a finite numerical certificate, enumerator, checker or numeric reduction.
-/

noncomputable section
open Polynomial Finset

namespace D5.S3.Analytic.KarpZhangCatalanPower.Coeff

/- proof_shape: bind-only definition; escape_witness: none;
consumer: Interval.Z, Interval.Z_symm, a_eq_polynomial, Index.a_hasDerivAt_poly, a_nonneg,
a_pos, a_product, a_zero_parameter, adjacent_ratio, adjacent_tp2, Index.b, Index.b_eq_poly,
Interval.derivative_difference, Index.hasDerivAt_a, Interval.hasDerivAt_slice, Index.index_law,
Interval.left_derivative_reindex, Interval.right_derivative_reindex, Interval.sliceDerivative,
Interval.sliceDerivative_pos, Interval.tail_nonneg, tp2, tp2_le. -/
/-- The literal rising-factorial quotient in formula (15). -/
def a (n : ℕ) (t : ℝ) : ℝ :=
  (ascPochhammer ℝ (2 * n)).eval t /
    ((ascPochhammer ℝ n).eval (t + 1) * (n.factorial : ℝ))

/- proof_shape: bind-only definition; escape_witness: none;
consumer: a_eq_polynomial, Index.a_hasDerivAt_poly, a_product, Index.b_eq_centralBinom,
Index.b_eq_poly, coeffPoly_succ_eval, Index.hasDerivAt_a, Index.index_law,
Index.index_polynomial, Index.natural_coeff, Index.natural_index. -/
/-- The polynomial continuation of the coefficient. -/
def coeffPoly : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C ((n + 1).factorial : ℝ)⁻¹ * X *
      (ascPochhammer ℝ n).comp (X + C (n + 2 : ℝ))

/- proof_shape: bind-only; escape_witness: none;
consumer: a_eq_polynomial, a_product, Index.natural_coeff. -/
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
consumer: Index.a_hasDerivAt_poly, a_product, Index.hasDerivAt_a, Index.index_law. -/
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
  calc
    _ = (-1 : ℝ) ^ n * (descPochhammer ℝ n).eval (-t) := by
      simpa only [neg_neg] using ascPochhammer_eval_neg_eq_descPochhammer ℝ (-t) n
    _ = (-1 : ℝ) ^ n * ∏ j ∈ range n, (-t - j) := by
      rw [descPochhammer_eval_eq_prod_range]
    _ = (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * ∏ j ∈ range n, (t + j)) := by
      congr 1
      calc
        _ = ∏ j ∈ range n, (-1 : ℝ) * (t + j) := by
          apply prod_congr rfl
          intro j hj
          ring
        _ = _ := by rw [prod_mul_distrib]; simp
    _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num

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
consumer: a_nonneg, adjacent_tp2, tp2. -/
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
consumer: Interval.tail_nonneg. -/
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
  ring

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
consumer: Interval.sliceDerivative_pos, tp2_le. -/
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
consumer: Interval.sliceDerivative_pos. -/
theorem tp2_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) {i l : ℕ} (hil : i < l) :
    a l u * a i v ≤ a i u * a l v := by
  rcases huv.eq_or_lt with rfl | h
  · exact le_of_eq (mul_comm _ _)
  · exact (tp2 hu h hil).le

end D5.S3.Analytic.KarpZhangCatalanPower.Coeff
end

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open PowerSeries Set
namespace D5.S3.Analytic.KarpZhangCatalanPower.Index
open P13CatalanLagrangeBridge
open D5.S3.Analytic.KarpZhangCatalanPower.Coeff

/- proof_shape: bind-only; escape_witness: none; consumer: natural_coeff. -/
private lemma natural_catalan_coeff (n t : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff n (catalanUnit ^ t) =
      ((2*n+t-1).choose n : ℚ) - ((2*n+t-1).choose (n-1) : ℚ) := by
  have hsub : subst q ((1 + PowerSeries.X : PowerSeries ℚ)^t) = catalanUnit ^ t := by
    have hs : HasSubst q := HasSubst.of_constantCoeff_zero' q_constantCoeff
    rw [subst_pow hs, subst_add hs, subst_X hs]
    have ho : subst q (1: PowerSeries ℚ) = 1 := by
      rw [← coe_substAlgHom hs, map_one]
    rw [ho]
    simp [q]
  have ht := q_subst_coefficient_transform ((1+PowerSeries.X)^t) n hn
  rw [hsub] at ht
  have hexp : 2*n-1+t=2*n+t-1 := by omega
  rw [mul_assoc, ← pow_add, hexp] at ht
  rw [one_sub_X_power_coefficient, ite_eq_right (by omega : n ≠ 0)] at ht
  exact ht

/- proof_shape: bind-only; escape_witness: none; consumer: natural_coeff. -/
private lemma choose_diff (n t : ℕ) :
    ((2*(n+1)+t-1).choose (n+1) : ℚ) - ((2*(n+1)+t-1).choose n : ℚ) =
      (t:ℚ) * (ascPochhammer ℚ n).eval ((t+n+2:ℕ):ℚ) / ((n+1).factorial : ℚ) := by
  have hnat := Nat.ascFactorial_eq_factorial_mul_choose (t+n+1) n
  have hexp : t+n+1+n=2*(n+1)+t-1 := by omega
  rw [hexp] at hnat
  rw [ascPochhammer_nat_eq_natCast_ascFactorial]
  have hcast : (((t+n+2).ascFactorial n : ℕ):ℚ) =
      (n.factorial:ℚ) * ((2*(n+1)+t-1).choose n :ℚ) := by
    exact_mod_cast hnat
  rw [hcast]
  have hchoose := Nat.choose_succ_right_eq (2*(n+1)+t-1) n
  have hchoose' : ((2*(n+1)+t-1).choose (n+1):ℚ) * ((n:ℚ)+1) =
      ((2*(n+1)+t-1).choose n : ℚ) * ((n:ℚ)+(t:ℚ)+1) := by
    have hn : 2*(n+1)+t-1-n=n+t+1 := by omega
    rw [hn] at hchoose
    exact_mod_cast hchoose
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfac : (n.factorial:ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hnp : (n:ℚ)+1 ≠ 0 := by positivity
  field_simp
  nlinarith




/- proof_shape: bind-only; escape_witness: none;
consumer: natural_index. -/
private lemma natural_coeff (n t : ℕ) :
    (coeffPoly n).eval (t:ℝ) = ((PowerSeries.coeff n (catalanUnit ^ t) : ℚ):ℝ) := by
  cases n with
  | zero => simp [coeffPoly, coeff_zero_eq_constantCoeff_apply, catalanUnit_constantCoeff]
  | succ n =>
    rw [natural_catalan_coeff (n+1) t (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [choose_diff]
    rw [coeffPoly_succ_eval]
    push_cast
    have hcast : (ascPochhammer ℝ n).eval ((t:ℝ)+n+2) =
        (((ascPochhammer ℚ n).eval ((t+n+2:ℕ):ℚ) : ℚ):ℝ) := by
      rw [ascPochhammer_eval₂ (Rat.castHom ℝ)]
      simpa only [Rat.coe_castHom, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat,
        Nat.cast_add, Nat.cast_ofNat] using
        Polynomial.eval₂_at_apply (p := ascPochhammer ℚ n)
          (Rat.castHom ℝ) ((t + n + 2 : ℕ) : ℚ)
    rw [hcast]
    push_cast
    rfl

/- proof_shape: bind-only; escape_witness: none;
consumer: index_polynomial. -/
private lemma natural_index (s t m : ℕ) :
    ∑ k ∈ Finset.range (m+1),
      (coeffPoly k).eval (s:ℝ) * (coeffPoly (m-k)).eval (t:ℝ) =
      (coeffPoly m).eval ((s:ℝ)+(t:ℝ)) := by
  have hc := congrArg (PowerSeries.coeff m) (pow_add catalanUnit s t)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  have hcR := congrArg (fun x:ℚ => (x:ℝ)) hc
  push_cast at hcR
  simp_rw [natural_coeff]
  rw [← Nat.cast_add, natural_coeff]
  exact hcR.symm

/- proof_shape: bind-only; escape_witness: none;
consumer: hasDerivAt_a, index_law. -/
theorem index_polynomial (s t : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m+1),
      (coeffPoly k).eval s * (coeffPoly (m-k)).eval t =
      (coeffPoly m).eval (s+t) := by
  classical
  have infiniteN : Set.Infinite (Set.range (fun n:ℕ => (n:ℝ))) :=
    Set.infinite_range_of_injective Nat.cast_injective
  have extension (t:ℕ) :
      (∑ k ∈ Finset.range (m+1),
        coeffPoly k * Polynomial.C ((coeffPoly (m-k)).eval (t:ℝ))) =
      (coeffPoly m).comp (Polynomial.X + Polynomial.C (t:ℝ)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply infiniteN.mono
    rintro x ⟨s,rfl⟩
    simpa only [Set.mem_ofPred_eq, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X] using natural_index s t m
  have extension' :
      (∑ k ∈ Finset.range (m+1),
        Polynomial.C ((coeffPoly k).eval s) * coeffPoly (m-k)) =
      (coeffPoly m).comp (Polynomial.C s + Polynomial.X) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply infiniteN.mono
    rintro x ⟨t,rfl⟩
    have ht := congrArg (Polynomial.eval s) (extension t)
    simpa only [Set.mem_ofPred_eq, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X] using ht
  have ht := congrArg (Polynomial.eval t) extension'
  simpa only [Set.mem_ofPred_eq, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X] using ht

/- proof_shape: bind-only; escape_witness: none;
consumer: Interval.tail_nonneg. -/
theorem index_law (s t : ℝ) (m : ℕ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∑ k ∈ Finset.range (m+1), a k s * a (m-k) t = a m (s+t) := by
  simp_rw [a_eq_polynomial _ (by linarith : -1<s),
    a_eq_polynomial _ (by linarith : -1<t)]
  rw [a_eq_polynomial _ (by linarith : -1<s+t)]
  exact index_polynomial s t m

/- proof_shape: bind-only; escape_witness: none;
consumer: b_eq_poly, hasDerivAt_a. -/
private lemma a_hasDerivAt_poly (n : ℕ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (a n) ((coeffPoly n).derivative.eval t) t := by
  apply ((coeffPoly n).hasDerivAt t).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact a_eq_polynomial n hx

/- proof_shape: bind-only definition; escape_witness: none;
consumer: b_eq_centralBinom, b_eq_poly, b_pos, Interval.derivative_difference, hasDerivAt_a,
Interval.hasDerivAt_slice, Interval.left_derivative_reindex, Interval.right_derivative_reindex,
Interval.sliceDerivative, Interval.sliceDerivative_pos. -/
/-- The positive infinitesimal coefficients of the convolution semigroup. -/
def b (j : ℕ) : ℝ := deriv (a j) 0

/- proof_shape: bind-only; escape_witness: none;
consumer: b_eq_centralBinom, hasDerivAt_a. -/
private lemma b_eq_poly (j : ℕ) : b j = (coeffPoly j).derivative.eval 0 :=
  (a_hasDerivAt_poly j (by norm_num)).deriv

/- proof_shape: bind-only; escape_witness: none;
consumer: b_pos. -/
theorem b_eq_centralBinom (j : ℕ) (hj : 1 ≤ j) :
    b j = ((2*j).choose j :ℝ)/(2*j) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  rw [b_eq_poly]
  have hb : (coeffPoly (n+1)).derivative.eval 0 =
      (ascPochhammer ℝ n).eval ((n:ℝ)+2) / ((n+1).factorial :ℝ) := by
    simp [coeffPoly, Polynomial.derivative_mul, Polynomial.derivative_comp,
      Polynomial.eval_comp, div_eq_mul_inv]
    ring
  rw [hb]
  have hf := Nat.ascFactorial_eq_factorial_mul_choose (n+1) n
  have he : n+1+n=2*n+1 := by omega
  rw [he] at hf
  have hreal : (ascPochhammer ℝ n).eval ((n:ℝ)+2) =
      (n.factorial:ℝ) * ((2*n+1).choose n:ℝ) := by
    rw [show (n:ℝ)+2=((n+2:ℕ):ℝ) by push_cast; ring,
      ascPochhammer_nat_eq_natCast_ascFactorial]
    exact_mod_cast hf
  rw [hreal, Nat.factorial_succ]
  have hc := Nat.choose_succ_succ' (2*n+1) n
  have hsym : (2*n+1).choose (n+1)=(2*n+1).choose n :=
    Nat.choose_symm_half n
  rw [hsym] at hc
  rw [show 2*n+1+1=2*(n+1) by omega] at hc
  have hcR : ((2*(n+1)).choose (n+1):ℝ)=2*((2*n+1).choose n:ℝ) := by
    have h := congrArg (fun x:ℕ => (x:ℝ)) hc
    push_cast at h
    linarith
  rw [hcR]
  have hfac : (n.factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hnp : (n:ℝ)+1≠0 := by positivity
  push_cast
  field_simp

/- proof_shape: bind-only; escape_witness: none;
consumer: Interval.sliceDerivative_pos. -/
theorem b_pos (j : ℕ) (hj : 1 ≤ j) : 0 < b j := by
  rw [b_eq_centralBinom j hj]
  apply div_pos
  · exact_mod_cast Nat.choose_pos (by omega : j≤2*j)
  · positivity

/- proof_shape: bind-only; escape_witness: none;
consumer: Interval.hasDerivAt_slice. -/
theorem hasDerivAt_a (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (a n) (∑ j ∈ Finset.Icc 1 n, b j * a (n-j) t) t := by
  have hleft : HasDerivAt
      (fun s:ℝ => ∑ j ∈ Finset.range (n+1),
        (coeffPoly j).eval s * (coeffPoly (n-j)).eval t)
      (∑ j ∈ Finset.range (n+1),
        (coeffPoly j).derivative.eval 0 * (coeffPoly (n-j)).eval t) 0 := by
    exact HasDerivAt.fun_sum (fun j _ =>
      ((coeffPoly j).hasDerivAt 0).mul_const ((coeffPoly (n-j)).eval t))
  have hright : HasDerivAt (fun s:ℝ => (coeffPoly n).eval (s+t))
      ((coeffPoly n).derivative.eval t) 0 := by
    simpa only [id_eq, zero_add, mul_one, Function.comp_def] using
      ((coeffPoly n).hasDerivAt (0+t)).comp 0 ((hasDerivAt_id 0).add_const t)
  have hfun : (fun s:ℝ => ∑ j ∈ Finset.range (n+1),
        (coeffPoly j).eval s * (coeffPoly (n-j)).eval t) =
      (fun s:ℝ => (coeffPoly n).eval (s+t)) := by
    funext s
    exact index_polynomial s t n
  rw [hfun] at hleft
  have hd := hright.unique hleft
  have hder := a_hasDerivAt_poly n (by linarith : -1<t)
  rw [hd] at hder
  convert hder using 1
  simp_rw [← b_eq_poly, ← a_eq_polynomial _ (by linarith : -1<t)]
  apply Finset.sum_subset
  · intro j hj
    have h := Finset.mem_Icc.mp hj
    exact Finset.mem_range.mpr (by omega)
  · intro j hj hnot
    have hj0 : j=0 := by
      have h := Finset.mem_range.mp hj
      have h' : ¬(1≤j ∧ j≤n) := by simpa only [Finset.mem_Icc] using hnot
      omega
    subst j
    simp [b_eq_poly, coeffPoly]

end D5.S3.Analytic.KarpZhangCatalanPower.Index
