/- GID: D5/S3/ArithSums/HannaA301310Divisibility
   generality: I
   mirror-B: D5/B/S3/ArithSums/HannaA301310Divisibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Geometric binomial averages and Hanna's A301310 divisibility conjecture. -/

/-
admission_basis: open-problem-resolution (#21832; Proved)
escape_witness: none; the module is admitted by its settling result.
Direct pre-existing frozen dependencies: none.
Source/provenance qualification: https://github.com/the-omega-institute/trureturing/issues/21832#issuecomment-6562357166
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22143
Source: https://oeis.org/A301310/internal, COMMENTS and FORMULA.
The source series is literal; proofs use Mathlib preHilbertPoly composed with X^2.
eval_diff: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: eval_diff_iter, inverse_half_even.
eval_diff_iter: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: eval_diff_iter_apply, diff_nilpotent.
eval_diff_iter_apply: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies:
none; consumers: coeff_cast, newton.
diff_nilpotent: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: inverse_eq.
inverse: proof_shape: bind-only (definition); escape_witness: none; Direct pre-existing frozen dependencies:
none; consumers: inverse_eq, inverse_half_even, numerator_neg_one.
diff_add: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: diff_sum.
diff_cmul: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: inverse_eq.
diff_sum: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: inverse_eq.
inverse_eq: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: inverse_half_even.
antiperiodic_zero: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: inverse_half_even.
inverse_half_even: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: numerator_neg_one.
coeff_cast: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: numerator_neg_one, series_value.
numerator: proof_shape: bind-only (definition); escape_witness: none; Direct pre-existing frozen dependencies:
none; consumers: numerator_degree, numerator_zero, numerator_neg_one, value_homogenize,
value_divisible.
numerator_degree: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: value_homogenize, value_divisible.
numerator_zero: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: value_divisible.
numerator_neg_one: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: value_divisible.
numerator_factor: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: value_divisible.
newton: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none; consumers:
series_value.
hasSum_choose: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: series_value.
value: proof_shape: bind-only (definition); escape_witness: none; Direct pre-existing frozen dependencies:
none; consumers: series_value, value_homogenize, value_divisible, polynomial_divisibility.
series_value: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: polynomial_divisibility.
value_homogenize: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: value_divisible.
value_divisible: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: polynomial_divisibility.
polynomial_divisibility: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies:
none; consumers: falling_hasSum, rising_hasSum.
falling_eval: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: falling_zero, falling_hasSum.
falling_degree: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: falling_hasSum.
falling_zero: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: falling_hasSum.
falling_even: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: falling_hasSum.
falling_hasSum: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: result, HannaA301432Divisibility.result.
rising_eval: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: rising_zero, rising_hasSum.
rising_degree: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: rising_hasSum.
rising_zero: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: rising_hasSum.
rising_even: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: rising_hasSum.
rising_hasSum: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: HannaA301311Divisibility.result.
a: proof_shape: bind-only (definition); escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: claim, result.
claim: proof_shape: bind-only (definition); escape_witness: none; Direct pre-existing frozen dependencies:
none; consumers: result.
result: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none; consumers:
none; settling result.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Analysis.SpecificLimits.Normed


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.HannaA301310Divisibility

open Polynomial Finset
open scoped fwdDiff


private theorem eval_diff (P : ℚ[X]) (x : ℚ) :
    ((fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X)).eval x = P.eval (x+1) - P.eval x := by
  simp [fwdDiff]

private theorem eval_diff_iter (P : ℚ[X]) (j : ℕ) :
    ((fun P : ℚ[X] => fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X)^[j] P).eval = (fwdDiff (1 : ℚ))^[j] P.eval := by
  exact (Function.Semiconj.iterate_right
    (f := fun Q : ℚ[X] => Q.eval)
    (ga := fun P : ℚ[X] => fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X)
    (gb := fwdDiff (1 : ℚ))
    (fun Q => by funext x; exact eval_diff Q x) j) P


private theorem eval_diff_iter_apply (P : ℚ[X]) (j : ℕ) (x : ℚ) :
    ((fun P : ℚ[X] => fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X)^[j] P).eval x = (fwdDiff (1:ℚ))^[j] P.eval x :=
  congrFun (eval_diff_iter P j) x

private theorem diff_nilpotent (P : ℚ[X]) {d : ℕ} (hd : P.natDegree ≤ d) :
    (fun P : ℚ[X] => fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X)^[d+1] P = 0 := by
  apply Polynomial.funext
  intro x
  have h := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (lt_of_le_of_lt hd (Nat.lt_succ_self d))
  have := congrFun h x
  simpa only [← eval_diff_iter, Pi.zero_apply, eval_zero] using this

private noncomputable def inverse (P : ℚ[X]) (d : ℕ) (m : ℚ) : ℚ[X] :=
  ∑ j ∈ range (d+1), C (m^j) * (fun P : ℚ[X] => fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X)^[j] P

private theorem diff_add (P Q : ℚ[X]) : (fwdDiff (1 : ℚ[X]) (fun R : ℚ[X] => (P+Q).comp R) X) = (fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X) + (fwdDiff (1 : ℚ[X]) (fun R : ℚ[X] => Q.comp R) X) := by
  simpa only [fwdDiff, Pi.add_apply, add_comp, comp_X] using
    congrFun (fwdDiff_add (1 : ℚ[X]) (fun R => P.comp R) (fun R => Q.comp R)) X

private theorem diff_cmul (c : ℚ) (P : ℚ[X]) : (fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => (C c * P).comp Q) X) = C c * (fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X) := by
  simpa only [fwdDiff, Pi.smul_apply, smul_eq_mul, mul_comp, C_comp, comp_X] using
    congrFun (fwdDiff_const_smul (1 : ℚ[X]) (C c) (fun R => P.comp R)) X

private theorem diff_sum (s : Finset ℕ) (P : ℕ → ℚ[X]) :
    (fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => (∑ j ∈ s, P j).comp Q) X) = ∑ j ∈ s, (fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => (P j).comp Q) X) := by
  let F : ℚ[X] →+ ℚ[X] :=
    { toFun := fun P => fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X
      map_zero' := by simp [fwdDiff]
      map_add' := diff_add }
  exact map_sum F P s

private theorem inverse_eq (P : ℚ[X]) {d : ℕ} (hd : P.natDegree ≤ d) (m : ℚ) :
    inverse P d m - C m * (fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => (inverse P d m).comp Q) X) = P := by
  have hs : C m * (fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => (inverse P d m).comp Q) X) =
      ∑ j ∈ range (d+1), C (m^(j+1)) * (fun P : ℚ[X] => fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X)^[j+1] P := by
    simp only [inverse, diff_sum, diff_cmul, Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [Function.iterate_succ_apply']
    rw [← mul_assoc, ← C_mul]
    congr 2
    ring
  rw [hs]
  have ht := sum_range_succ' (fun j => C (m^j) * (fun P : ℚ[X] => fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X)^[j] P) d
  have ht' := sum_range_succ (fun j => C (m^(j+1)) * (fun P : ℚ[X] => fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X)^[j+1] P) d
  simp only [diff_nilpotent P hd, mul_zero, add_zero] at ht'
  simp only [pow_zero, C_1, one_mul, Function.iterate_zero_apply] at ht
  dsimp only [inverse]
  rw [ht', ht]
  abel

private theorem antiperiodic_zero (Q : ℚ[X])
    (hQ : ∀ x : ℚ, Q.eval (x+1) = - Q.eval x) : Q = 0 := by
  have hs : Function.Semiconj (fun c : ℚ => fun x : ℚ => c * Q.eval x)
      (fun c : ℚ => (-2) * c) (fwdDiff (1 : ℚ)) := by
    intro c
    funext x
    dsimp [fwdDiff]
    rw [hQ]
    ring
  have hi (j : ℕ) : (fwdDiff (1 : ℚ))^[j] Q.eval = fun x => (-2:ℚ)^j * Q.eval x := by
    have h := Function.Semiconj.iterate_right hs j (1 : ℚ)
    simpa only [mul_left_iterate_apply_one, one_mul] using h.symm
  have h := Q.fwdDiff_iter_degree_add_one_eq_zero
  rw [hi] at h
  apply Polynomial.funext
  intro x
  have hx := congrFun h x
  have hn : (-2:ℚ)^(Q.natDegree+1) ≠ 0 := pow_ne_zero _ (by norm_num)
  simpa only [Pi.zero_apply, mul_eq_zero, hn, false_or, eval_zero] using hx

private theorem inverse_half_even (P : ℚ[X]) {d : ℕ} (hd : P.natDegree ≤ d)
    (he : ∀ x : ℚ, P.eval (-x) = P.eval x) :
    (inverse P d (-1/2)).eval 0 = P.eval 0 := by
  let Q := inverse P d (-1/2)
  have hq (x : ℚ) : Q.eval x + Q.eval (x+1) = 2 * P.eval x := by
    have h := congrArg (Polynomial.eval x) (inverse_eq P hd (-1/2))
    simp only [eval_sub, eval_mul, eval_C, eval_diff] at h
    change Q.eval x - (-1/2) * (Q.eval (x+1) - Q.eval x) = P.eval x at h
    linarith
  let R := Q.comp (-X) - Q.comp (X+1)
  have hz : R = 0 := by
    apply antiperiodic_zero
    intro x
    dsimp [R]
    simp only [eval_sub, eval_comp, eval_neg, eval_X, eval_add, eval_one]
    have h1 := hq (-(x+1))
    have h2 := hq (x+1)
    rw [he] at h1
    have hx : -(x+1)+1 = -x := by ring
    rw [hx] at h1
    linarith
  have h0 := congrArg (Polynomial.eval 0) hz
  dsimp [R] at h0
  simp only [eval_sub, eval_comp, eval_neg, eval_X, eval_add, eval_one, neg_zero,
    zero_add, eval_zero] at h0
  have h := hq 0
  norm_num only [zero_add] at h
  simpa only [Q] using (show Q.eval 0 = P.eval 0 by linarith)


private theorem coeff_cast (P : ℚ[X]) (f : ℕ → ℤ)
    (hf : ∀ k : ℕ, P.eval (k:ℚ) = (f k : ℚ)) (j : ℕ) :
    ((((fwdDiff (1:ℕ))^[j] f 0) : ℤ) : ℚ) = ((fun P : ℚ[X] => fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X)^[j] P).eval 0 := by
  rw [eval_diff_iter_apply]
  simp only [ fwdDiff_iter_eq_sum_shift, zero_add, nsmul_eq_mul,
    zsmul_eq_mul, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast, Nat.cast_id, mul_one, hf]

private noncomputable def numerator (f : ℕ → ℤ) (d : ℕ) : ℤ[X] :=
  ∑ j ∈ range (d+1), C (((fwdDiff (1:ℕ))^[j] f 0)) * X^j * (1-X)^(d-j)

private theorem numerator_degree (f : ℕ → ℤ) (d : ℕ) :
    (numerator f d).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjd : j ≤ d := by exact mem_range_succ_iff.mp hj
  apply (natDegree_mul_le).trans
  apply (add_le_add (natDegree_C_mul_X_pow_le _ _) (natDegree_pow_le)).trans
  simpa using (show j + (d-j) * (1-X : ℤ[X]).natDegree ≤ d by
    have hx : (1-X : ℤ[X]).natDegree ≤ 1 := by
      apply (natDegree_sub_le _ _).trans
      simp
    nlinarith [Nat.sub_add_cancel hjd])

private theorem numerator_zero (P : ℚ[X]) (f : ℕ → ℤ)
    (hf : ∀ k : ℕ, P.eval (k:ℚ) = (f k : ℚ)) (h0 : P.eval 0 = 0) (d : ℕ) :
    (numerator f d).eval 0 = 0 := by
  have hz : ((fwdDiff (1:ℕ))^[0] f 0) = 0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [Function.iterate_zero_apply, Int.cast_zero, Nat.cast_zero]
      using (hf 0).symm.trans h0
  simp [numerator, eval_finsetSum, hz, sum_range_succ']

private theorem numerator_neg_one (P : ℚ[X]) (f : ℕ → ℤ)
    (hf : ∀ k : ℕ, P.eval (k:ℚ) = (f k : ℚ)) {d : ℕ} (hd : P.natDegree ≤ d)
    (h0 : P.eval 0 = 0) (he : ∀ x : ℚ, P.eval (-x) = P.eval x) :
    (numerator f d).eval (-1) = 0 := by
  have hm : (inverse P d (-1/2)).eval 0 = 0 :=
    (inverse_half_even P hd he).trans h0
  apply Int.cast_injective (α := ℚ)
  push_cast
  calc
    (((numerator f d).eval (-1) : ℤ) : ℚ) =
        (2:ℚ)^d * (inverse P d (-1/2)).eval 0 := by
      simp only [numerator, inverse, eval_finsetSum, eval_mul, eval_C, eval_pow,
        eval_X, eval_sub, eval_one, Int.cast_sum, Int.cast_mul, Int.cast_pow,
        Int.cast_neg, Int.cast_one, sub_neg_eq_add, one_add_one_eq_two, mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [coeff_cast P f hf]
      have hjd : j ≤ d := Nat.le_of_lt_succ (mem_range.mp hj)
      have hp : (2:ℚ)^d = 2^j * 2^(d-j) := by exact (pow_mul_pow_sub 2 hjd).symm
      rw [hp, div_pow]
      field_simp
      ring
    _ = 0 := by rw [hm, mul_zero]

private theorem numerator_factor (N : ℤ[X]) {d : ℕ}
    (hd : N.natDegree ≤ d) (h0 : N.eval 0 = 0) (h1 : N.eval (-1) = 0)
    (h2 : 2 ≤ d) :
    ∃ Q : ℤ[X], N = X * (X+1) * Q ∧ Q.natDegree ≤ d-2 := by
  have hx : (X : ℤ[X]) ∣ N := by
    exact Polynomial.X_dvd_iff.mpr (by rw [coeff_zero_eq_eval_zero]; exact h0)
  obtain ⟨M, hm⟩ := hx
  have hm1 : M.eval (-1) = 0 := by
    rw [hm, eval_mul, eval_X] at h1
    norm_num at h1 ⊢
    exact h1
  have hx1 : X+1 ∣ M := by
    simpa using (Polynomial.dvd_iff_isRoot.mpr hm1)
  obtain ⟨Q, hq⟩ := hx1
  refine ⟨Q, by rw [hm, hq]; ring, ?_⟩
  by_cases hz : Q = 0
  · simp [hz]
  have hdeg : (X * (X+1) * Q).natDegree = 2 + Q.natDegree := by
    rw [natDegree_mul (mul_ne_zero X_ne_zero (by simpa using (monic_X_add_C (1:ℤ)).ne_zero)) hz,
      natDegree_mul X_ne_zero (by simpa using (monic_X_add_C (1:ℤ)).ne_zero)]
    simp
  have hh : N = X*(X+1)*Q := by rw [hm, hq]; ring
  rw [hh, hdeg] at hd
  omega


private theorem newton (P : ℚ[X]) {d : ℕ} (hd : P.natDegree ≤ d) (k : ℕ) :
    P.eval (k:ℚ) = ∑ j ∈ range (d+1), (k.choose j : ℚ) * ((fun P : ℚ[X] => fwdDiff (1 : ℚ[X]) (fun Q : ℚ[X] => P.comp Q) X)^[j] P).eval 0 := by
  have hn := shift_eq_sum_fwdDiff_iter (1:ℚ) P.eval k 0
  simp only [nsmul_eq_mul, mul_one, zero_add, ← eval_diff_iter_apply] at hn
  rw [hn]
  by_cases hk : k ≤ d
  · apply sum_subset (range_mono (Nat.add_le_add_right hk 1))
    intro j hjd hjk
    have hkj : k < j := by simp only [mem_range] at hjd hjk; omega
    rw [Nat.choose_eq_zero_of_lt hkj, Nat.cast_zero, zero_mul]
  · symm
    apply sum_subset (range_mono (by omega : d+1 ≤ k+1))
    intro j hjk hjd
    have hdj : P.natDegree < j := by simp only [mem_range] at hjk hjd; omega
    have hz := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdj) 0
    rw [eval_diff_iter_apply]
    rw [show (fwdDiff (1:ℚ))^[j] P.eval 0 = 0 from hz, mul_zero]

private theorem hasSum_choose (j : ℕ) {r : ℝ} (hr : ‖r‖ < 1) :
    HasSum (fun k : ℕ => (k.choose j : ℝ) * r^k) (r^j/(1-r)^(j+1)) := by
  have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  convert (hasSum_descFactorial_mul_geometric_of_norm_lt_one j hr).div_const
    (j.factorial : ℝ) using 1
  · ext k
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    field_simp
  · field_simp

private noncomputable def value (f : ℕ → ℤ) (d : ℕ) (m : ℤ) : ℤ :=
  ∑ j ∈ range (d+1), ((fwdDiff (1:ℕ))^[j] f 0) * m^j

private theorem series_value (P : ℚ[X]) (f : ℕ → ℤ)
    (hf : ∀ k : ℕ, P.eval (k:ℚ) = (f k : ℚ)) {d : ℕ} (hd : P.natDegree ≤ d)
    (m : ℕ) :
    HasSum (fun k : ℕ => (m:ℝ)^k * (f k:ℝ) / (m+1:ℝ)^(k+1))
      (value f d m : ℝ) := by
  let r : ℝ := m / (m+1)
  have hm0 : (m+1:ℝ) ≠ 0 := by exact Nat.cast_add_one_ne_zero m
  have hr : ‖r‖ < 1 := by
    dsimp [r]
    rw [abs_of_nonneg (by positivity)]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hn (k : ℕ) : (f k : ℝ) =
      ∑ j ∈ range (d+1), ((((fwdDiff (1:ℕ))^[j] f 0) : ℤ) : ℝ) * (k.choose j : ℝ) := by
    have h := newton P hd k
    rw [hf] at h
    simp_rw [← coeff_cast P f hf] at h
    have h' : (f k : ℚ) =
        ∑ j ∈ range (d+1), ((((fwdDiff (1:ℕ))^[j] f 0) : ℤ) : ℚ) * (k.choose j : ℚ) := by
      simpa only [mul_comm] using h
    exact_mod_cast h'
  have hs := hasSum_sum (s := range (d+1)) (fun j _ =>
    ((hasSum_choose j hr).mul_left ((((fwdDiff (1:ℕ))^[j] f 0) : ℤ) : ℝ)).div_const (m+1:ℝ))
  convert hs using 1
  · ext k
    rw [hn]
    simp only [mul_sum, sum_div]
    apply sum_congr rfl
    intro j hj
    dsimp [r]
    rw [div_pow, pow_succ]
    field_simp
  · simp only [value, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    apply sum_congr rfl
    intro j hj
    dsimp [r]
    have hsub : 1 - (m:ℝ)/(m+1) = 1/(m+1) := by field_simp; ring
    rw [hsub, div_pow, div_pow, one_pow, pow_succ]
    field_simp

private theorem value_homogenize (f : ℕ → ℤ) (d m : ℕ) :
    value f d m = MvPolynomial.eval ![(m:ℤ), m+1] ((numerator f d).homogenize d) := by
  apply Int.cast_injective (α := ℚ)
  have hv := MvPolynomial.map_eval (Int.castRingHom ℚ) ![(m:ℤ), m+1]
    ((numerator f d).homogenize d)
  rw [← homogenize_map] at hv
  have hm0 : ((Int.castRingHom ℚ) ∘ ![(m:ℤ), m+1]) 1 ≠ 0 := by exact Ne.symm (not_eq_of_beq_eq_false rfl)
  rw [eval_homogenize (natDegree_map_le.trans (numerator_degree f d)) _ hm0] at hv
  change (value f d m : ℚ) = (Int.castRingHom ℚ) _
  rw [hv]
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.coe_castRingHom, Int.cast_natCast, Int.cast_add, Int.cast_one,
    numerator, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
    Polynomial.map_sub, Polynomial.map_one, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X, eval_sub, eval_one, value, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast, Finset.sum_mul]
  apply sum_congr rfl
  intro j hj
  have hjd : j ≤ d := Nat.le_of_lt_succ (mem_range.mp hj)
  have hm0 : (m+1:ℚ) ≠ 0 := by exact Nat.cast_add_one_ne_zero m
  have hsub : 1-(m:ℚ)/(m+1) = 1/(m+1) := by field_simp; ring
  rw [hsub, div_pow, div_pow, one_pow]
  have hp : (m+1:ℚ)^d = (m+1)^j * (m+1)^(d-j) := by
    exact (pow_mul_pow_sub (m+1:ℚ) hjd).symm
  rw [hp]
  field_simp

private theorem value_divisible (P : ℚ[X]) (f : ℕ → ℤ)
    (hf : ∀ k : ℕ, P.eval (k:ℚ) = (f k : ℚ)) {d : ℕ} (hd : P.natDegree ≤ d)
    (h0 : P.eval 0 = 0) (he : ∀ x : ℚ, P.eval (-x) = P.eval x)
    (h2 : 2 ≤ d) (m : ℕ) : ∃ q : ℤ, value f d m = (m:ℤ)*(2*m+1)*q := by
  obtain ⟨Q, hN, hQ⟩ := numerator_factor (numerator f d) (numerator_degree f d)
    (numerator_zero P f hf h0 d) (numerator_neg_one P f hf hd h0 he) h2
  refine ⟨MvPolynomial.eval ![(m:ℤ), m+1] (Q.homogenize (d-2)), ?_⟩
  rw [value_homogenize, hN]
  have hdeg : (X*(X+1) : ℤ[X]).natDegree ≤ 2 := by
    apply (natDegree_mul_le).trans
    norm_num
  have hsplit : d = 2+(d-2) := by exact (Nat.add_sub_of_le h2).symm
  have hmul := homogenize_mul (X*(X+1) : ℤ[X]) Q hdeg hQ
  rw [← hsplit] at hmul
  rw [hmul]
  have hfac : (X*(X+1) : ℤ[X]).homogenize 2 =
      MvPolynomial.X 0 * (MvPolynomial.X 0 + MvPolynomial.X 1) := by
    convert homogenize_mul (X : ℤ[X]) (X+1) (m := 1) (n := 1) (by simp) (by simp) using 1
    simp only [homogenize_add, homogenize_X (by decide : 1 ≠ 0),
      homogenize_one, Nat.sub_self, pow_zero, pow_one, mul_one]
  rw [hfac]
  simp only [map_mul, MvPolynomial.eval_X, map_add, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  congr 1
  ring

/-- Every even rational polynomial vanishing at zero, with integral natural values,
    has a geometric average divisible by m(2m+1). -/
private theorem polynomial_divisibility (P : ℚ[X]) (f : ℕ → ℤ)
    (hf : ∀ k : ℕ, P.eval (k:ℚ) = (f k : ℚ)) {d : ℕ} (hd : P.natDegree ≤ d)
    (h0 : P.eval 0 = 0) (he : ∀ x : ℚ, P.eval (-x) = P.eval x)
    (h2 : 2 ≤ d) (m : ℕ) :
    ∃ q : ℤ, HasSum
      (fun k : ℕ => (m:ℝ)^k * (f k:ℝ) / (m+1:ℝ)^(k+1))
      ((m:ℝ)*(2*m+1)*(q:ℝ)) := by
  obtain ⟨q, hq⟩ := value_divisible P f hf hd h0 he h2 m
  refine ⟨q, ?_⟩
  have hs := series_value P f hf hd m
  rw [hq] at hs
  exact_mod_cast hs

private theorem falling_eval (n k : ℕ) :
    ((preHilbertPoly ℚ n n).comp (X^2)).eval (k:ℚ) =
      (Nat.choose (k^2) n : ℚ) := by
  rw [eval_comp, eval_pow, eval_X, ← Nat.cast_pow]
  simpa only [Nat.add_sub_cancel] using
    preHilbertPoly_eq_choose_add_sub ℚ n (k := n) (n := k^2) (by omega)

private theorem falling_degree (n : ℕ) :
    ((preHilbertPoly ℚ n n).comp (X^2)).natDegree ≤ 2*n := by
  rw [natDegree_comp, natDegree_preHilbertPoly, natDegree_pow, natDegree_X]
  omega

private theorem falling_zero (n : ℕ) (hn : 0 < n) :
    ((preHilbertPoly ℚ n n).comp (X^2)).eval 0 = 0 := by
  simpa [Nat.choose_eq_zero_of_lt hn] using falling_eval n 0

private theorem falling_even (n : ℕ) (x : ℚ) :
    ((preHilbertPoly ℚ n n).comp (X^2)).eval (-x) =
      ((preHilbertPoly ℚ n n).comp (X^2)).eval x := by
  simp

theorem falling_hasSum (n : ℕ) (hn : 0 < n) (m : ℕ) :
    ∃ q : ℤ, HasSum (fun k : ℕ =>
      (m:ℝ)^k * (Nat.choose (k^2) n : ℝ) / (m+1:ℝ)^(k+1))
      ((m:ℝ)*(2*m+1)*(q:ℝ)) := by
  exact polynomial_divisibility ((preHilbertPoly ℚ n n).comp (X^2))
    (fun k => Nat.choose (k^2) n)
    (fun k => by simpa using falling_eval n k) (falling_degree n)
    (falling_zero n hn) (falling_even n) (by omega : 2 ≤ 2*n) m

private theorem rising_eval (n k : ℕ) (hn : 0 < n) :
    ((preHilbertPoly ℚ n 1).comp (X^2)).eval (k:ℚ) =
      (Nat.choose (k^2+n-1) n : ℚ) := by
  rw [eval_comp, eval_pow, eval_X, ← Nat.cast_pow]
  exact preHilbertPoly_eq_choose_add_sub ℚ n (k := 1) (n := k^2) (by omega)

private theorem rising_degree (n : ℕ) :
    ((preHilbertPoly ℚ n 1).comp (X^2)).natDegree ≤ 2*n := by
  rw [natDegree_comp, natDegree_preHilbertPoly, natDegree_pow, natDegree_X]
  omega

private theorem rising_zero (n : ℕ) (hn : 0 < n) :
    ((preHilbertPoly ℚ n 1).comp (X^2)).eval 0 = 0 := by
  simpa [Nat.choose_eq_zero_of_lt (show n-1 < n by omega)] using rising_eval n 0 hn

private theorem rising_even (n : ℕ) (x : ℚ) :
    ((preHilbertPoly ℚ n 1).comp (X^2)).eval (-x) =
      ((preHilbertPoly ℚ n 1).comp (X^2)).eval x := by
  simp

theorem rising_hasSum (n : ℕ) (hn : 0 < n) (m : ℕ) :
    ∃ q : ℤ, HasSum (fun k : ℕ =>
      (m:ℝ)^k * (Nat.choose (k^2+n-1) n : ℝ) / (m+1:ℝ)^(k+1))
      ((m:ℝ)*(2*m+1)*(q:ℝ)) := by
  exact polynomial_divisibility ((preHilbertPoly ℚ n 1).comp (X^2))
    (fun k => Nat.choose (k^2+n-1) n)
    (fun k => by simpa using rising_eval n k hn) (rising_degree n)
    (rising_zero n hn) (rising_even n) (by omega : 2 ≤ 2*n) m


/-- OEIS A301310, third FORMULA line, interpreted as a convergent real series. -/
noncomputable def a (n : ℕ) : ℝ :=
  ∑' k : ℕ, (2 : ℝ) ^ k * (Nat.choose (k ^ 2) n : ℝ) / (3 : ℝ) ^ (k + 1)

/-- OEIS A301310, second COMMENTS line: a(n) is divisible by 10 for n > 0. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ q : ℤ, a n = (10 : ℝ) * (q : ℝ)



theorem result : claim := by
  intro n hn
  obtain ⟨q, hq⟩ := falling_hasSum n (by omega) 2
  refine ⟨q, ?_⟩
  norm_num only [Nat.cast_ofNat] at hq
  simpa only [a] using hq.tsum_eq


end D5.S3.ArithSums.HannaA301310Divisibility
