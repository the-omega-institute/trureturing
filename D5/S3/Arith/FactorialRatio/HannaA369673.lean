/- GID: D5/S3/Arith/FactorialRatio/HannaA369673
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/HannaA369673
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's square classification and exact five-adic orders for OEIS A369673. -/

/-
Public theorem: D5.S3.Arith.FactorialRatio.HannaA369673.result
proof_shape: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#21915; Proved)
Direct frozen dependencies: Erdos7.finset_prod_odd_nat (GID D5/S3/Arith/Congruence/ConditionalComparison/ArithmeticCoordinates.finset_prod_odd_nat; statement_id sha256:ca6f4774d9134cf720bde8cd822095dcdb127a0243d3249701a758fd2033ed3c).
The source product and signed factorial difference retain their source expressions.
All helpers below have proof_shape: bind-only and escape_witness: none;
their frozen frontier after same-module expansion is Erdos7.finset_prod_odd_nat
for Q_odd, a_even_square, a_even_twoVal, square_classification; it is empty for the other helpers.
Consumers are listed after each name.
a_pos: a_even_square.
a_step: a_even, a_odd_square, a_odd_not_five.
Q_step: a_even, five_Q_step.
a_even: a_even_twoVal, a_even_square, five_a_even.
a_odd_square: square_classification.
Q_pos: a_even_twoVal, five_Q_step, five_a_even.
Q_odd: a_even_twoVal; Erdos7.finset_prod_odd_nat (frozen owner above).
a_even_twoVal: a_even_square.
a_even_square: square_classification.
square_classification: result.
odd_two_factor: a_odd_not_five.
a_odd_not_five: result.
five_even_factor: five_Q_even.
five_odd_factor: five_Q_even, five_Q_odd.
five_Q_step: five_Q_even, five_Q_odd.
five_Q_even: five_Q_odd, result.
five_Q_odd: result.
S_factorial: S_eq_b.
S_eq_b: result.
five_a_even: result.
Definitions a, b, claim, Q and S have proof_shape: bind-only; escape_witness: none.
Their direct frozen dependencies are none.
a: claim, a_pos, a_step, a_even, a_odd_square, a_odd_not_five.
b: claim, S_eq_b. claim: result.
Private implementation definitions: Q : ℕ → ℕ; S : ℕ → ℕ.
Q: Q_step, a_even, Q_pos, Q_odd. S: five_Q_even, five_Q_odd, S_factorial, S_eq_b.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22235.
-/

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.NumberTheory.Multiplicity
import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Arith.FactorialRatio.HannaA369673

/-- OEIS A369673 NAME: the product includes both k = 0 and k = N. -/
def a (N : ℕ) : ℕ :=
  ∏ k ∈ Finset.range (N + 1), ((2 : ℕ) ^ k + 2 ^ (N - k))

/-- OEIS A127428 NAME, using signed subtraction literally. -/
def b (n : ℕ) : ℤ :=
  (padicValNat 5 (Nat.factorial (10 * n)) : ℤ) -
    (padicValNat 5 (Nat.factorial (5 * n)) : ℤ)

/-- The entire four-clause conjecture package, without a parameter restriction. -/
def claim : Prop :=
  (∀ N : ℕ, IsSquare (a N) ↔ ¬ (4 : ℕ) ∣ N) ∧
  (∀ n : ℕ, ¬ (5 : ℕ) ∣ a (2 * n + 1)) ∧
  (∀ n : ℕ, (padicValNat 5 (a (4 * n)) : ℤ) = 2 * b n) ∧
  (∀ n : ℕ, (padicValNat 5 (a (4 * n + 2)) : ℤ) = 2 * b (n + 1))

end D5.S3.Arith.FactorialRatio.HannaA369673

namespace D5.S3.Arith.FactorialRatio.HannaA369673

private theorem a_pos (N : ℕ) : 0 < a N := by
  unfold a
  exact Finset.prod_pos (fun k hk => by positivity)

private theorem a_step (N : ℕ) :
    a (N + 2) = 2 ^ (N + 1) * (1 + 2 ^ (N + 2)) ^ 2 * a N := by
  unfold a
  rw [show N + 2 + 1 = (N + 1) + 1 + 1 by omega, Finset.prod_range_succ,
      Finset.prod_range_succ']
  have hp : (∏ k ∈ Finset.range (N + 1),
      (2 ^ (k + 1) + 2 ^ (N + 2 - (k + 1)))) =
      2 ^ (N + 1) * (∏ k ∈ Finset.range (N + 1), (2 ^ k + 2 ^ (N - k))) := by
    calc
      _ = ∏ k ∈ Finset.range (N + 1), 2 * (2 ^ k + 2 ^ (N - k)) := by
        apply Finset.prod_congr rfl
        intro k hk
        have hk' : k ≤ N := by exact Finset.mem_range_succ_iff.mp hk
        rw [show N + 2 - (k + 1) = (N - k) + 1 by omega]
        simp only [pow_succ]
        ring
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [hp]
  simp only [Nat.sub_self, Nat.sub_zero, pow_zero]
  ring


private def Q (m : ℕ) : ℕ := ∏ j ∈ Finset.range m, (1 + 4 ^ (j + 1))

private theorem Q_step (m : ℕ) : Q (m + 1) = Q m * (1 + 4 ^ (m + 1)) := by
  simp only [Q, Finset.prod_range_succ]

private theorem a_even (m : ℕ) : a (2 * m) = 2 ^ (m ^ 2 + 1) * Q m ^ 2 := by
  induction m with
  | zero => norm_num [a, Q]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, a_step, ih]
    have hp : (2 : ℕ) ^ (2 * m + 2) = 4 ^ (m + 1) := by
      rw [show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul]
      rfl
    rw [hp]
    rw [Q_step]
    calc
      _ = 2 ^ ((2 * m + 1) + (m ^ 2 + 1)) *
          (Q m * (1 + 4 ^ (m + 1))) ^ 2 := by rw [pow_add]; ring
      _ = _ := by congr 2; ring

private theorem a_odd_square (m : ℕ) : IsSquare (a (2 * m + 1)) := by
  induction m with
  | zero => refine ⟨3, ?_⟩; norm_num [a, Finset.prod_range_succ]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, a_step]
    exact ((Even.isSquare_pow (show Even (2 * m + 1 + 1) from
      ⟨m + 1, by omega⟩) 2).mul (IsSquare.sq _)).mul ih


private theorem Q_pos (m : ℕ) : 0 < Q m := by
  unfold Q
  exact Finset.prod_pos (fun j hj => by positivity)

private theorem Q_odd (m : ℕ) : Odd (Q m) := by
  unfold Q
  exact Erdos7.finset_prod_odd_nat (Finset.range m) _ (fun j _ =>
    ((show Even (4 : ℕ) from ⟨2, rfl⟩).pow_of_ne_zero
      (by omega : j + 1 ≠ 0)).one_add)

private theorem a_even_twoVal (m : ℕ) : padicValNat 2 (a (2 * m)) = m ^ 2 + 1 := by
  rw [a_even, padicValNat.mul (by positivity) (by have := Q_pos m; positivity),
    padicValNat.prime_pow, padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd (Q_odd m).not_two_dvd_nat]

private theorem a_even_square (m : ℕ) : IsSquare (a (2 * m)) ↔ Odd m := by
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by intro h; rw [h] at hr; have := a_pos (2 * m); simp_all
    have hv := congrArg (padicValNat 2) hr
    rw [a_even_twoVal, padicValNat.mul hr0 hr0] at hv
    have he : Even (m ^ 2 + 1) := ⟨padicValNat 2 r, hv⟩
    exact (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp
      (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp he))
  · intro hm
    rw [a_even]
    exact ((hm.pow).add_one.isSquare_pow 2).mul (IsSquare.sq _)

private theorem square_classification (N : ℕ) : IsSquare (a N) ↔ ¬ (4 : ℕ) ∣ N := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' N
  · subst N
    rw [a_even_square, Nat.odd_iff]
    constructor
    · intro h hd
      obtain ⟨k, hk⟩ := hd
      have : m = 2 * k := by omega
      omega
    · intro h
      have hm := Nat.mod_lt m (by decide : 0 < 2)
      by_contra hn
      have hz : m % 2 = 0 := by exact Nat.mod_two_ne_one.mp hn
      have he := Nat.mod_add_div m 2
      apply h
      exact ⟨m / 2, by omega⟩
  · subst N
    constructor
    · intro h hd
      obtain ⟨k, hk⟩ := hd
      omega
    · intro h
      exact a_odd_square m


private theorem odd_two_factor (m : ℕ) : ¬ (5 : ℕ) ∣ (1 + 2 ^ (2 * m + 1)) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
  · subst m
    have he : 2 * (2 * k) + 1 = 4 * k + 1 := by omega
    rw [he, pow_add, pow_mul]
    intro h
    have h0 := Nat.mod_eq_zero_of_dvd h
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at h0
  · subst m
    have he : 2 * (2 * k + 1) + 1 = 4 * k + 3 := by omega
    rw [he, pow_add, pow_mul]
    intro h
    have h0 := Nat.mod_eq_zero_of_dvd h
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at h0

private theorem a_odd_not_five (m : ℕ) : ¬ (5 : ℕ) ∣ a (2 * m + 1) := by
  induction m with
  | zero => norm_num [a, Finset.prod_range_succ]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, a_step]
    intro hd
    rcases Nat.prime_five.dvd_mul.mp hd with h | h
    · rcases Nat.prime_five.dvd_mul.mp h with h2 | hf
      · have := Nat.prime_five.dvd_of_dvd_pow h2
        norm_num at this
      · apply odd_two_factor (m + 1)
        convert Nat.prime_five.dvd_of_dvd_pow hf using 1
    · exact ih h

private theorem five_even_factor (j : ℕ) : padicValNat 5 (1 + 4 ^ (2 * j + 2)) = 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have h0 := Nat.mod_eq_zero_of_dvd h
  rw [show 2 * j + 2 = 2 * (j + 1) by omega, pow_mul] at h0
  norm_num [Nat.add_mod, Nat.pow_mod] at h0

private theorem five_odd_factor (j : ℕ) :
    padicValNat 5 (1 + 4 ^ (2 * j + 1)) = 1 + padicValNat 5 (2 * j + 1) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := padicValNat.pow_add_pow (p := 5) (x := 4) (y := 1)
    (by decide : Odd 5) (by norm_num) (by norm_num) (odd_two_mul_add_one j)
  simpa [add_comm, padicValNat_base (by decide : 1 < 5)] using h

private theorem five_Q_step (m : ℕ) : padicValNat 5 (Q (m + 1)) =
    padicValNat 5 (Q m) + padicValNat 5 (1 + 4 ^ (m + 1)) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Q_step, padicValNat.mul (Q_pos m).ne' (by positivity)]

private def S (r : ℕ) : ℕ := ∑ j ∈ Finset.range r, (1 + padicValNat 5 (2 * j + 1))

private theorem five_Q_even (r : ℕ) : padicValNat 5 (Q (2 * r)) = S r := by
  induction r with
  | zero => simp [Q, S]
  | succ r ih =>
    rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, five_Q_step, five_Q_step,
      show 2 * r + 1 + 1 = 2 * r + 2 by omega, five_even_factor, five_odd_factor, ih]
    simp only [S, Finset.sum_range_succ]
    omega

private theorem five_Q_odd (r : ℕ) : padicValNat 5 (Q (2 * r + 1)) = S (r + 1) := by
  rw [five_Q_step, five_Q_even, five_odd_factor]
  simp only [S, Finset.sum_range_succ]

private theorem S_factorial (r : ℕ) : (S r : ℤ) = (r : ℤ) +
    (padicValNat 5 (2 * r).factorial : ℤ) - (padicValNat 5 r.factorial : ℤ) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  induction r with
  | zero => simp [S]
  | succ r ih =>
    have hf : (2 * (r + 1)).factorial =
        (2 * r + 2) * ((2 * r + 1) * (2 * r).factorial) := by
      exact Nat.add_zero ((Nat.mul 2 r + 1).succ.mul (Nat.mul 2 r + 1).factorial)
    have hv : padicValNat 5 (2 * r + 2) = padicValNat 5 (r + 1) := by
      rw [show 2 * r + 2 = 2 * (r + 1) by omega,
        padicValNat.mul (by decide : (2 : ℕ) ≠ 0) (by omega)]
      norm_num [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬(5 : ℕ) ∣ 2)]
    rw [hf, Nat.factorial_succ,
      padicValNat.mul (by omega : 2 * r + 2 ≠ 0) (by positivity),
      padicValNat.mul (by omega : 2 * r + 1 ≠ 0) (Nat.factorial_ne_zero _),
      padicValNat.mul (by omega : r + 1 ≠ 0) (Nat.factorial_ne_zero _), hv]
    simp only [S, Finset.sum_range_succ] at *
    push_cast at *
    omega

private theorem S_eq_b (r : ℕ) : (S r : ℤ) = b r := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h10 := padicValNat_factorial_mul (p := 5) (2 * r)
  have h5 := padicValNat_factorial_mul (p := 5) r
  rw [show 5 * (2 * r) = 10 * r by omega] at h10
  rw [b, h10, h5, S_factorial]
  push_cast
  ring

private theorem five_a_even (m : ℕ) : padicValNat 5 (a (2 * m)) = 2 * padicValNat 5 (Q m) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [a_even, padicValNat.mul (by positivity) (by have := Q_pos m; positivity),
    padicValNat.pow, padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬(5 : ℕ) ∣ 2)]
  omega

theorem result : claim := by
  refine ⟨square_classification, a_odd_not_five, ?_, ?_⟩
  · intro n
    rw [show 4 * n = 2 * (2 * n) by omega, five_a_even, five_Q_even]
    push_cast
    rw [S_eq_b]
  · intro n
    rw [show 4 * n + 2 = 2 * (2 * n + 1) by omega, five_a_even, five_Q_odd]
    push_cast
    rw [S_eq_b]

end D5.S3.Arith.FactorialRatio.HannaA369673
