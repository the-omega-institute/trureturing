/- GID: D5/S3/Analytic/MeijerZeroCount/Rodrigues
   generality: G
   mirror-B: D5/B/S3/Analytic/MeijerZeroCount/Rodrigues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.LocalExtr.Polynomial, mathlib/module/Mathlib.Algebra.Polynomial.Derivative, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Positivity, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Data.Nat.Choose.Cast, mathlib/module/Mathlib.Tactic.FieldSimp, mathlib/module/Mathlib.Tactic.Push, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Rodrigues expansions and exact interior zero counts for compactly supported Mellin kernels. -/

import D5.S3.Analytic.MeijerZeroCount.Defs
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Polynomial Finset
open scoped BigOperators
noncomputable section
namespace D5.S3.Analytic.MeijerZeroCount.Rodrigues

def W (n N : ℕ) : ℝ[X] := X ^ n * (1 - X) ^ N

def coeffA (n d k : ℕ) : ℝ :=
  (-1) ^ (n + k) * (n + k).factorial /
    ((k.factorial : ℝ) ^ 2 * ((n + d - 1 - k).factorial : ℝ))

def rodriguesPoly (n d : ℕ) : ℝ[X] :=
  C ((-1 : ℝ) ^ n / ((n + d - 1).factorial : ℝ)) *
    derivative^[n] (W n (n + d - 1))

def f (n d : ℕ) (c x : ℝ) : ℂ :=
  if x ∈ Set.Ioo 0 1 then
    ((x ^ ((n : ℝ) + c) : ℝ) : ℂ) * (((rodriguesPoly n d).eval x : ℝ) : ℂ)
  else 0

private lemma W_sum (n N : ℕ) :
    W n N = ∑ k ∈ range (N+1), C ((-1:ℝ)^k * (N.choose k:ℝ)) * X^(n+k) := by
  have h : (1-X : ℝ[X])^N =
      ∑ k ∈ range (N+1), C ((-1:ℝ)^k * (N.choose k:ℝ)) * X^k := by
    rw [show (1-X : ℝ[X]) = -X+1 by ring, add_pow]
    apply sum_congr rfl
    intro k hk
    rw [neg_pow]
    simp only [one_pow, mul_one, map_mul, map_pow, map_neg, map_one, C_eq_natCast]
    ring
  rw [W, h, mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

private lemma coefficient_identity (n N k : ℕ) (hk : k ≤ N) :
    (-1:ℝ)^n / (N.factorial:ℝ) *
      (((-1:ℝ)^k * (N.choose k:ℝ)) * ((n+k).descFactorial n:ℝ)) =
    (-1:ℝ)^(n+k) * ((n+k).factorial:ℝ) /
      ((k.factorial:ℝ)^2 * ((N-k).factorial:ℝ)) := by
  have hfac : (k.factorial:ℝ) * ((n+k).descFactorial n:ℝ) = ((n+k).factorial:ℝ) := by
    exact_mod_cast (by simpa using Nat.factorial_mul_descFactorial (show n ≤ n+k by omega))
  rw [Nat.cast_choose ℝ hk, pow_add]
  have hN : (N.factorial:ℝ) ≠ 0 := by positivity
  have hkf : (k.factorial:ℝ) ≠ 0 := by positivity
  have hNk : ((N-k).factorial:ℝ) ≠ 0 := by positivity
  rw [← hfac]
  field_simp (discharger := first | assumption | positivity)

private theorem rodriguesPoly_eq_sum (n d : ℕ) :
    rodriguesPoly n d = ∑ k ∈ range (n+d-1+1), C (coeffA n d k) * X^k := by
  rw [rodriguesPoly, W_sum, iterate_derivative_sum, mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul]
  simp only [Nat.add_sub_cancel_left]
  rw [← mul_assoc, ← C_mul, ← mul_assoc, ← C_mul]
  congr 2
  dsimp only [coeffA]
  simpa only [mul_assoc] using
    coefficient_identity n (n+d-1) k (Nat.le_of_lt_succ (mem_range.mp hk))

theorem f_eq_sum (n d : ℕ) (c x : ℝ) (hx : x ∈ Set.Ioo 0 1) :
    f n d c x = ∑ k ∈ range (n+d-1+1),
      (coeffA n d k:ℂ) * ((x^((n:ℝ)+c+k):ℝ):ℂ) := by
  rw [f, ite_eq_left hx, rodriguesPoly_eq_sum]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow, mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [Real.rpow_add hx.1 ((n:ℝ)+c) (k:ℝ), Real.rpow_natCast]
  push_cast
  ring

private lemma W_coeff (n N : ℕ) : (W n N).coeff n = 1 := by
  have h0 : ((1 - X : ℝ[X]) ^ N).coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, eval_pow, eval_sub, eval_one, eval_X]
    simp
  calc
    (W n N).coeff n = ((1 - X : ℝ[X]) ^ N).coeff 0 := by
      simpa only [W, zero_add] using
        (coeff_X_pow_mul ((1 - X : ℝ[X]) ^ N) n 0)
    _ = 1 := h0

private lemma W_derivative_ne_zero (n N k : ℕ) (hk : k ≤ n) :
    derivative^[k] (W n N) ≠ 0 := by
  intro he
  have hc := congrArg (fun p : ℝ[X] => p.coeff (n - k)) he
  rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, W_coeff] at hc
  simp only [nsmul_eq_mul, mul_one, coeff_zero, Nat.cast_eq_zero] at hc
  exact (Nat.descFactorial_pos.mpr hk).ne' hc

private lemma W_endpoint_zero (n N k : ℕ) (hk : k < n) :
    (derivative^[k] (W n N)).eval 0 = 0 := by
  obtain ⟨q, hq⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd k
    (show (X : ℝ[X]) ^ n ∣ W n N from dvd_mul_right _ _)
  rw [hq]
  simp [Nat.sub_ne_zero_of_lt hk]

private lemma W_endpoint_one (n N k : ℕ) (hk : k < N) :
    (derivative^[k] (W n N)).eval 1 = 0 := by
  obtain ⟨q, hq⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd k
    (show (1 - X : ℝ[X]) ^ N ∣ W n N from dvd_mul_left _ _)
  rw [hq]
  simp [Nat.sub_ne_zero_of_lt hk]

private def interiorRoots (p : ℝ[X]) : Finset ℝ :=
  p.roots.toFinset.filter (fun x => x ∈ Set.Ioo 0 1)

private lemma mem_interiorRoots (p : ℝ[X]) (hp : p ≠ 0) (x : ℝ) :
    x ∈ interiorRoots p ↔ x ∈ Set.Ioo 0 1 ∧ p.eval x = 0 := by
  dsimp only [interiorRoots]
  simp only [mem_filter, Multiset.mem_toFinset, mem_roots hp, IsRoot]
  exact and_comm

private lemma rolle_count (p : ℝ[X]) (hp : p ≠ 0) (hp' : p.derivative ≠ 0)
    (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 0) :
    (interiorRoots p).card + 1 ≤ (interiorRoots p.derivative).card := by
  let S := insert (0 : ℝ) (insert 1 (interiorRoots p))
  have hc : S.card ≤ (interiorRoots p.derivative).card + 1 := by
    apply Finset.card_le_of_interleaved
    intro x hx y hy hxy _
    have hs (z : ℝ) (hz : z ∈ S) : 0 ≤ z ∧ z ≤ 1 ∧ p.eval z = 0 := by
      simp only [S, mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact ⟨le_rfl, zero_le_one, h0⟩
      · exact ⟨zero_le_one, le_rfl, h1⟩
      · obtain ⟨hz, he⟩ := (mem_interiorRoots p hp z).mp hz
        exact ⟨hz.1.le, hz.2.le, he⟩
    obtain ⟨z, hz, hdz⟩ := exists_deriv_eq_zero hxy p.continuousOn ((hs x hx).2.2.trans (hs y hy).2.2.symm)
    refine ⟨z, (mem_interiorRoots p.derivative hp' z).mpr ⟨?_, ?_⟩, hz⟩
    · exact ⟨lt_of_le_of_lt (hs x hx).1 hz.1, lt_of_lt_of_le hz.2 (hs y hy).2.1⟩
    · simpa only [← Polynomial.deriv] using hdz
  have hcS : S.card = (interiorRoots p).card + 2 := by
    have h0' : (0 : ℝ) ∉ interiorRoots p := by
      dsimp only [interiorRoots]
      simp
    have h1' : (1 : ℝ) ∉ interiorRoots p := by
      dsimp only [interiorRoots]
      simp
    simp [S, h0', h1']
  omega

private lemma W_interior_lower (n N k : ℕ) (hk : k ≤ n) (hN : n ≤ N) :
    k ≤ (interiorRoots (derivative^[k] (W n N))).card := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hkn : k < n := by omega
    have hkN : k < N := lt_of_lt_of_le hkn hN
    have hcount := rolle_count (derivative^[k] (W n N))
      (W_derivative_ne_zero n N k (by omega))
      (by simpa only [← Function.iterate_succ_apply' derivative k (W n N)] using W_derivative_ne_zero n N (k+1) hk)
      (W_endpoint_zero n N k hkn) (W_endpoint_one n N k hkN)
    rw [← Function.iterate_succ_apply' derivative k (W n N)] at hcount
    exact (Nat.succ_le_succ (ih (by omega))).trans hcount

private lemma W_interior_upper (n N : ℕ) (hN : n ≤ N) :
    (interiorRoots (derivative^[n] (W n N))).card ≤ n := by
  have hne := W_derivative_ne_zero n N n le_rfl
  obtain ⟨q, hq⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd n
    (show (1 - X : ℝ[X]) ^ N ∣ W n N from dvd_mul_left _ _)
  have hqne : q ≠ 0 := by intro h; simp [h] at hq; exact hne hq
  have hfne : ((1 - X : ℝ[X]) ^ (N - n)) ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm (by simpa using (X_ne_C (1 : ℝ)))))
  have hdegree : (1 - (X : ℝ[X])).natDegree = 1 := by
    rw [natDegree_sub]
    simpa using natDegree_X_sub_C (1 : ℝ)
  have hdW : (W n N).natDegree ≤ n + N := by
    calc
      (W n N).natDegree ≤ (X ^ n : ℝ[X]).natDegree + ((1 - X : ℝ[X]) ^ N).natDegree :=
        natDegree_mul_le
      _ = n + N := by simp [natDegree_pow, hdegree]
  have hd : q.natDegree ≤ n := by
    have hb := (W n N).natDegree_iterate_derivative n
    rw [hq, natDegree_mul hfne hqne, natDegree_pow, hdegree, mul_one] at hb
    omega
  have hs : interiorRoots (derivative^[n] (W n N)) ⊆ q.roots.toFinset := by
    intro x hx
    obtain ⟨hx, he⟩ := (mem_interiorRoots _ hne x).mp hx
    rw [hq, eval_mul, eval_pow, eval_sub, eval_one, eval_X] at he
    have hxne : (1 - x) ^ (N - n) ≠ 0 := pow_ne_zero _ (by linarith [hx.2])
    have hqx : q.eval x = 0 := (mul_eq_zero.mp he).resolve_left hxne
    simpa only [Multiset.mem_toFinset, mem_roots hqne, IsRoot] using hqx
  exact (Finset.card_le_card hs).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' q).trans hd))

/-- The nth derivative of X^n(1-X)^N has exactly n distinct roots in (0,1). -/
private theorem zeros_W_derivative (n N : ℕ) (hN : n ≤ N) :
    {x : ℝ | x ∈ Set.Ioo 0 1 ∧ (derivative^[n] (W n N)).eval x = 0}.encard = n := by
  have he : {x : ℝ | x ∈ Set.Ioo 0 1 ∧ (derivative^[n] (W n N)).eval x = 0} =
      (interiorRoots (derivative^[n] (W n N)) : Set ℝ) := by
    ext x
    exact (mem_interiorRoots _ (W_derivative_ne_zero n N n le_rfl) x).symm
  rw [he, Set.encard_coe_eq_coe_finsetCard]
  congr 1
  exact Nat.le_antisymm (W_interior_upper n N hN) (W_interior_lower n N n le_rfl hN)

/-- The compactly supported Rodrigues function has exactly n zeros in (0,1). -/
theorem zeros_f (n d : ℕ) (c : ℝ) (hd : 1 ≤ d) :
    {x : ℝ | x ∈ Set.Ioo 0 1 ∧ f n d c x = 0}.encard = n := by
  have hscalar : (-1 : ℝ) ^ n / ((n + d - 1).factorial : ℝ) ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)
  have he : {x : ℝ | x ∈ Set.Ioo 0 1 ∧ f n d c x = 0} =
      {x : ℝ | x ∈ Set.Ioo 0 1 ∧ (derivative^[n] (W n (n+d-1))).eval x = 0} := by
    ext x
    change (x ∈ Set.Ioo 0 1 ∧ f n d c x = 0) ↔
      (x ∈ Set.Ioo 0 1 ∧ (derivative^[n] (W n (n+d-1))).eval x = 0)
    apply and_congr_right
    intro hx
    have hp : (x ^ ((n : ℝ) + c) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx.1 _).ne'
    rw [f, ite_eq_left hx, ← Complex.ofReal_mul, Complex.ofReal_eq_zero]
    simp only [mul_eq_zero, hp, false_or]
    rw [rodriguesPoly, eval_mul, eval_C, mul_eq_zero]
    simp only [hscalar, false_or]
  rw [he]
  exact zeros_W_derivative n (n+d-1) (by omega)

end D5.S3.Analytic.MeijerZeroCount.Rodrigues
