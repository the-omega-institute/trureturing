/- GID: D5/S3/Combinatorics/DerangedMatchingCongruence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DerangedMatchingCongruence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Richman's conjecture in OEIS A053871 (2023): for a(n) = 2(n - 1)(a(n - 1) + a(n - 2)) with a(0) = 1, a(1) = 0 (deranged matchings, central moments of the chi-squared distribution) and every odd q, (-1)^m a(m) and (-1)^n a(n) are congruent modulo q whenever m and n are. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: the signed sequence
  b(n) = (-1)^n a(n) satisfies b(n + 2) = 2(n + 1)(b(n) - b(n + 1)) (`b_rec`) and equals the
  alternating sum of (-1)^k C(n, k) (2k - 1)!! (`c_succ`, `d_succ`, `c_rec`, `b_eq_c`); for odd q
  each term with k at least 1 of that sum at n = q is divisible by q, since
  2^k C(q, k) (2k - 1)!! = q (q - 1) ... (q - k + 1) C(2k, k) (`term_dvd`), so b(q) is 1 = b(0)
  and b(q + 1) is 0 = b(1) modulo q (`b_q`, `b_q1`); the recurrence coefficient has period q
  modulo q, so b(n + q) is b(n) modulo q for every n (`period`), and b modulo q depends only on
  the index modulo q
admission_basis: open-problem-resolution (issue #10354)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DerangedMatchingCongruence

open Nat

/-- A053871: `a(n) = 2 (n - 1) (a(n - 1) + a(n - 2))` with `a(0) = 1`, `a(1) = 0`. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => 2 * (n + 1) * (a (n + 1) + a n)

/-- Richman's conjecture in A053871. -/
def claim : Prop :=
  ∀ q m n : ℕ, Odd q → m ≡ n [MOD q] →
    (-1 : ℤ) ^ m * (a m : ℤ) ≡ (-1) ^ n * (a n : ℤ) [ZMOD q]

/-- The signed sequence `(-1)^n a(n)`. -/
private def b (n : ℕ) : ℤ := (-1) ^ n * (a n : ℤ)

/-- `Σ_k (-1)^k C(n, k) (2k - 1)!!`. -/
private def c (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (n.choose k : ℤ) * ((2 * k - 1)‼ : ℤ)

/-- `Σ_k (-1)^k C(n, k) (2k + 1)!!`. -/
private def d (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (n.choose k : ℤ) * ((2 * k + 1)‼ : ℤ)

theorem result : claim := by
  -- the signed recurrence
  have b_rec : ∀ n, b (n + 2) = 2 * (n + 1) * (b n - b (n + 1)) := by
    intro n
    simp only [b, a]
    push_cast
    ring
  have two_succ : ∀ k, 2 * (k + 1) - 1 = 2 * k + 1 := fun k => by omega
  -- `c` with its first term split off
  have c_shift : ∀ n, c n = 1 + ∑ k ∈ Finset.range n,
      (-1) ^ (k + 1) * (n.choose (k + 1) : ℤ) * ((2 * k + 1)‼ : ℤ) := by
    intro n
    unfold c
    rw [Finset.sum_range_succ']
    simp only [two_succ, Nat.choose_zero_right, pow_zero, Nat.cast_one, one_mul, mul_zero,
      Nat.zero_sub]
    rw [show ((0‼ : ℕ) : ℤ) = 1 by rfl]
    ring
  -- Pascal
  have c_succ : ∀ n, c (n + 1) = c n - d n := by
    intro n
    have h := Finset.sum_choose_succ_mul (R := ℤ) (fun i _ => (-1 : ℤ) ^ i * ((2 * i - 1)‼ : ℤ)) n
    unfold c d
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    convert h using 1
    · exact Finset.sum_congr rfl fun k _ => by ring
    · congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · exact Finset.sum_congr rfl fun k _ => by rw [two_succ]; ring
  -- the second relation: `d (n + 1) = c (n + 1) - 2 (n + 1) d n`
  have d_succ : ∀ n, d (n + 1) = c (n + 1) - 2 * (n + 1) * d n := by
    intro n
    have hE : ∑ k ∈ Finset.range (n + 1 + 1), (-1 : ℤ) ^ k * (k : ℤ) * ((n + 1).choose k : ℤ) *
        ((2 * k - 1)‼ : ℤ) = -((n : ℤ) + 1) * d n := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
      unfold d
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have h := Nat.add_one_mul_choose_eq n j
      have h' : ((j : ℤ) + 1) * ((n + 1).choose (j + 1) : ℤ) =
          ((n : ℤ) + 1) * (n.choose j : ℤ) := by
        exact_mod_cast (by rw [h]; ring : (j + 1) * (n + 1).choose (j + 1) = (n + 1) * n.choose j)
      rw [two_succ]
      push_cast
      linear_combination (-1 : ℤ) ^ (j + 1) * ((2 * j + 1)‼ : ℤ) * h'
    calc d (n + 1) = ∑ k ∈ Finset.range (n + 1 + 1), ((-1 : ℤ) ^ k * ((n + 1).choose k : ℤ) *
          ((2 * k - 1)‼ : ℤ) + 2 * ((-1 : ℤ) ^ k * (k : ℤ) * ((n + 1).choose k : ℤ) *
          ((2 * k - 1)‼ : ℤ))) := by
          unfold d
          apply Finset.sum_congr rfl
          intro k _
          rw [Nat.doubleFactorial_add_one (2 * k)]
          push_cast
          ring
      _ = c (n + 1) + 2 * (-((n : ℤ) + 1) * d n) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hE]
          rfl
      _ = c (n + 1) - 2 * (n + 1) * d n := by ring
  -- so `c` satisfies the signed recurrence
  have c_rec : ∀ n, c (n + 2) = 2 * (n + 1) * (c n - c (n + 1)) := by
    intro n
    have h1 := c_succ (n + 1)
    have h2 := d_succ n
    have h3 := c_succ n
    rw [h1, h2]
    linear_combination (2 * ((n : ℤ) + 1)) * h3
  have b_eq_c : ∀ n, b n = c n ∧ b (n + 1) = c (n + 1) := by
    intro n
    induction n with
    | zero =>
      constructor
      · simp [b, c, a]
      · simp [b, c, a, Finset.sum_range_succ]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [b_rec, c_rec, ih.1, ih.2]
  intro q m n hq hmn
  have hq0 : 0 < q := by obtain ⟨r, rfl⟩ := hq; omega
  -- each term of `c q` past the first is divisible by `q`
  have term_dvd : ∀ k, q ∣ q.choose (k + 1) * (2 * k + 1)‼ := by
    intro k
    have key : 2 ^ (k + 1) * (q.choose (k + 1) * (2 * k + 1)‼) =
        q.descFactorial (k + 1) * (2 * (k + 1)).choose (k + 1) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (k + 1))
      have hfac : (2 * (k + 1))! = 2 ^ (k + 1) * (k + 1)! * (2 * k + 1)‼ := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_eq_mul_doubleFactorial,
          show (2 * k + 1) + 1 = 2 * (k + 1) by ring, Nat.doubleFactorial_two_mul]
      have hc := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ 2 * (k + 1) by omega)
      rw [show 2 * (k + 1) - (k + 1) = k + 1 by omega] at hc
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      calc 2 ^ (k + 1) * (q.choose (k + 1) * (2 * k + 1)‼) * (k + 1)!
          = q.choose (k + 1) * (2 * (k + 1))! := by rw [hfac]; ring
        _ = q.choose (k + 1) * ((2 * (k + 1)).choose (k + 1) * (k + 1)! * (k + 1)!) := by
          rw [hc]
        _ = (k + 1)! * q.choose (k + 1) * (2 * (k + 1)).choose (k + 1) * (k + 1)! := by ring
    have hdesc : q ∣ q.descFactorial (k + 1) := by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [Nat.succ_descFactorial_succ]
      exact Dvd.intro _ rfl
    have hcop : q.Coprime (2 ^ (k + 1)) := (Nat.coprime_two_right.2 hq).pow_right _
    apply hcop.dvd_of_dvd_mul_left
    rw [key]
    exact Dvd.dvd.mul_right hdesc _
  have b_q : b q ≡ b 0 [ZMOD q] := by
    rw [(b_eq_c q).1, c_shift q, show b 0 = 1 by simp [b, a], Int.modEq_iff_dvd]
    rw [show (1 : ℤ) - (1 + ∑ k ∈ Finset.range q, (-1) ^ (k + 1) * (q.choose (k + 1) : ℤ) *
      ((2 * k + 1)‼ : ℤ)) = -∑ k ∈ Finset.range q, (-1) ^ (k + 1) * (q.choose (k + 1) : ℤ) *
      ((2 * k + 1)‼ : ℤ) by ring]
    apply Dvd.dvd.neg_right
    apply Finset.dvd_sum
    intro k _
    rw [mul_assoc]
    apply Dvd.dvd.mul_left
    exact_mod_cast term_dvd k
  have b_q1 : b (1 + q) ≡ b 1 [ZMOD q] := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [show 1 + (q' + 1) = q' + 2 by ring, b_rec, show b 1 = 0 by simp [b, a],
      Int.modEq_iff_dvd]
    rw [show (0 : ℤ) - 2 * ((q' : ℤ) + 1) * (b q' - b (q' + 1)) =
      ((q' + 1 : ℕ) : ℤ) * (-2 * (b q' - b (q' + 1))) by push_cast; ring]
    exact Dvd.intro _ rfl
  -- one period
  have period : ∀ n, b (n + q) ≡ b n [ZMOD q] ∧ b (n + 1 + q) ≡ b (n + 1) [ZMOD q] := by
    intro n
    induction n with
    | zero => exact ⟨by rw [zero_add]; exact b_q, by rw [zero_add]; exact b_q1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hcoef : (2 : ℤ) * ((n + q : ℕ) + 1) ≡ 2 * ((n : ℤ) + 1) [ZMOD q] := by
        rw [Int.modEq_iff_dvd]
        exact ⟨-2, by push_cast; ring⟩
      rw [show n + 1 + 1 + q = (n + q) + 2 by ring, b_rec, b_rec]
      rw [show n + q + 1 = n + 1 + q by ring]
      exact hcoef.mul (ih.1.sub ih.2)
  -- `b` modulo `q` is periodic with period `q`, so it depends only on the index modulo `q`
  have hp : Function.Periodic (fun i : ℕ => b i % (q : ℤ)) q := fun i => (period i).1
  have hm : b (m % q) % (q : ℤ) = b m % q := hp.map_mod_nat m
  have hn : b (n % q) % (q : ℤ) = b n % q := hp.map_mod_nat n
  change b m % q = b n % q
  rw [← hm, ← hn, show m % q = n % q from hmn]

end D5.S3.Combinatorics.DerangedMatchingCongruence
