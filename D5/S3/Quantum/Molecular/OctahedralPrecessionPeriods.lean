/- GID: D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods
   generality: G
   mirror-B: D5/B/S3/Quantum/Molecular/OctahedralPrecessionPeriods
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Bradley Klee's 2018 conjecture in OEIS A318245 that the scaled coefficients a(n) of the period of J-vector precession on the rotational energy surface of an octahedral molecule are integers divisible by 3 for n >= 1. -/

/-
proof_shape: result: content
escape_witness: form (1): the closed form a(n) = sum over k + j = n of
  C(2k,k) C(2j,j) C(2k+j,k) 4^j, obtained from the recurrence by the telescoping certificate
  `mid` and the summation `hrec`, and the congruence `mult`,
  b(3m + r) = b(r) b(m) mod 3, obtained from Lucas' theorem through `T3` and `term`
admission_basis: open-problem-resolution (issue #11173)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Molecular.OctahedralPrecessionPeriods

open Finset

/-!
OEIS A318245 (Bradley Klee, 2018): the scaled generating function
T(v) = Σ a(n) (3v/64)^n of the period of J-vector precession on the rotational energy surface of
an octahedral molecule satisfies 9(5v-4)T + d/dv(16v(v-1)(3v-4)T') = 0 with a(0) = 1. Comparing
coefficients gives a(1) = 12 and 3n²a(n) = 4(28n²-28n+9)a(n-1) - 64(4n-5)(4n-3)a(n-2) for n ≥ 2.
The entry conjectures that a(n) ≡ 0 (mod 3) for n > 0.
-/

/-- The sequence of OEIS A318245 over ℚ: `a 0 = 1`, `a 1 = 12` (forced by the ODE at v⁰) and
`3n²a(n) = 4(28n²-28n+9)a(n-1) - 64(4n-5)(4n-3)a(n-2)` for `n ≥ 2`. -/
def a : ℕ → ℚ
  | 0 => 1
  | 1 => 12
  | n + 2 => (4 * (28 * ((n : ℚ) + 2) ^ 2 - 28 * ((n : ℚ) + 2) + 9) * a (n + 1) -
      64 * (4 * ((n : ℚ) + 2) - 5) * (4 * ((n : ℚ) + 2) - 3) * a n) / (3 * ((n : ℚ) + 2) ^ 2)

/-- Klee's conjecture: for `n > 0`, `a n` is an integer divisible by 3. -/
def claim : Prop := ∀ n : ℕ, 0 < n → ∃ z : ℤ, a n = 3 * z

theorem result : claim := by
  -- summand
  let t : ℕ → ℕ → ℕ := fun k j =>
    Nat.centralBinom k * Nat.centralBinom j * Nat.choose (2 * k + j) k * 4 ^ j
  have R1 : ∀ k j, t k (j + 1) * ((j + 1) * (k + j + 1)) =
      t k j * (8 * (2 * j + 1) * (2 * k + j + 1)) := by
    intro k j
    have F1 := Nat.succ_mul_centralBinom_succ j
    have F2 := Nat.choose_mul_succ_eq (2 * k + j) k
    rw [show 2 * k + j + 1 - k = k + j + 1 by omega] at F2
    show Nat.centralBinom k * Nat.centralBinom (j + 1) * Nat.choose (2 * k + (j + 1)) k *
        4 ^ (j + 1) * ((j + 1) * (k + j + 1)) =
      Nat.centralBinom k * Nat.centralBinom j * Nat.choose (2 * k + j) k * 4 ^ j *
        (8 * (2 * j + 1) * (2 * k + j + 1))
    rw [show 2 * k + (j + 1) = 2 * k + j + 1 by ring]
    calc Nat.centralBinom k * Nat.centralBinom (j + 1) * Nat.choose (2 * k + j + 1) k *
          4 ^ (j + 1) * ((j + 1) * (k + j + 1))
        = Nat.centralBinom k * ((j + 1) * Nat.centralBinom (j + 1)) *
          (Nat.choose (2 * k + j + 1) k * (k + j + 1)) * 4 ^ (j + 1) := by ring
      _ = Nat.centralBinom k * (2 * (2 * j + 1) * Nat.centralBinom j) *
          (Nat.choose (2 * k + j) k * (2 * k + j + 1)) * 4 ^ (j + 1) := by rw [F1, F2]
      _ = _ := by ring
  have R3 : ∀ k j, t (k + 1) j * (4 * (k + 1) ^ 2 * (2 * j + 1)) =
      t k (j + 1) * ((2 * k + 1) * (j + 1) * (2 * k + j + 2)) := by
    intro k j
    have F1 := Nat.succ_mul_centralBinom_succ k
    have F2 := Nat.succ_mul_centralBinom_succ j
    have F3 := Nat.add_one_mul_choose_eq (2 * k + j + 1) k
    show Nat.centralBinom (k + 1) * Nat.centralBinom j * Nat.choose (2 * (k + 1) + j) (k + 1) *
        4 ^ j * (4 * (k + 1) ^ 2 * (2 * j + 1)) =
      Nat.centralBinom k * Nat.centralBinom (j + 1) * Nat.choose (2 * k + (j + 1)) k *
        4 ^ (j + 1) * ((2 * k + 1) * (j + 1) * (2 * k + j + 2))
    rw [show 2 * (k + 1) + j = 2 * k + j + 1 + 1 by ring, show 2 * k + (j + 1) = 2 * k + j + 1 by ring]
    calc Nat.centralBinom (k + 1) * Nat.centralBinom j * Nat.choose (2 * k + j + 1 + 1) (k + 1) *
          4 ^ j * (4 * (k + 1) ^ 2 * (2 * j + 1))
        = ((k + 1) * Nat.centralBinom (k + 1)) * Nat.centralBinom j *
          (Nat.choose (2 * k + j + 1 + 1) (k + 1) * (k + 1)) * 4 ^ j * (4 * (2 * j + 1)) := by ring
      _ = (2 * (2 * k + 1) * Nat.centralBinom k) * Nat.centralBinom j *
          ((2 * k + j + 1 + 1) * Nat.choose (2 * k + j + 1) k) * 4 ^ j * (4 * (2 * j + 1)) := by
        rw [F1, F3]
      _ = Nat.centralBinom k * (2 * (2 * j + 1) * Nat.centralBinom j) *
          Nat.choose (2 * k + j + 1) k * 4 ^ (j + 1) * ((2 * k + 1) * (2 * k + j + 2)) := by ring
      _ = _ := by rw [← F2]; ring
  -- the certificate factor
  let R : ℚ → ℚ → ℚ := fun n k =>
    2 * k ^ 2 * n * (4 * k * n - 4 * n ^ 2 + 6 * n - 3) /
      ((n + k) * (n + k - 1) * (2 * n - 2 * k - 1))
  -- one step of the telescoping sum
  have mid : ∀ k j : ℕ,
      3 * ((k : ℚ) + j + 2) ^ 2 * (t k (j + 2) : ℚ)
        - 4 * (28 * ((k : ℚ) + j + 2) ^ 2 - 28 * ((k : ℚ) + j + 2) + 9) * (t k (j + 1) : ℚ)
        + 64 * (4 * ((k : ℚ) + j + 2) - 5) * (4 * ((k : ℚ) + j + 2) - 3) * (t k j : ℚ)
      = (t (k + 1) (j + 1) : ℚ) * R ((k : ℚ) + j + 2) ((k : ℚ) + 1)
        - (t k (j + 2) : ℚ) * R ((k : ℚ) + j + 2) (k : ℚ) := by
    intro k j
    have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have E1 : (t k (j + 1) : ℚ) * ((j + 1) * (k + j + 1)) =
        (t k j : ℚ) * (8 * (2 * j + 1) * (2 * k + j + 1)) := by exact_mod_cast R1 k j
    have E2 : (t k (j + 1 + 1) : ℚ) * ((j + 1 + 1) * (k + (j + 1) + 1)) =
        (t k (j + 1) : ℚ) * (8 * (2 * (j + 1) + 1) * (2 * k + (j + 1) + 1)) := by
      exact_mod_cast R1 k (j + 1)
    have E3 : (t (k + 1) (j + 1) : ℚ) * (4 * (k + 1) ^ 2 * (2 * (j + 1) + 1)) =
        (t k (j + 1 + 1) : ℚ) * ((2 * k + 1) * (j + 1 + 1) * (2 * k + (j + 1) + 2)) := by
      exact_mod_cast R3 k (j + 1)
    have h1 : (t k (j + 1) : ℚ) = (t k j : ℚ) * (8 * (2 * j + 1) * (2 * k + j + 1)) /
        ((j + 1) * (k + j + 1)) := by
      rw [eq_div_iff (by positivity)]; exact E1
    have h2 : (t k (j + 2) : ℚ) = (t k (j + 1) : ℚ) * (8 * (2 * (j + 1) + 1) *
        (2 * k + (j + 1) + 1)) / ((j + 1 + 1) * (k + (j + 1) + 1)) := by
      rw [eq_div_iff (by positivity)]; exact E2
    have h3 : (t (k + 1) (j + 1) : ℚ) = (t k (j + 2) : ℚ) * ((2 * k + 1) * (j + 1 + 1) *
        (2 * k + (j + 1) + 2)) / (4 * (k + 1) ^ 2 * (2 * (j + 1) + 1)) := by
      rw [eq_div_iff (by positivity)]; exact E3
    rw [h3, h2, h1]
    simp only [R]
    rw [show ((k : ℚ) + j + 2 + (k + 1)) * ((k : ℚ) + j + 2 + (k + 1) - 1) *
        (2 * ((k : ℚ) + j + 2) - 2 * (k + 1) - 1) = (2 * k + j + 3) * (2 * k + j + 2) * (2 * j + 1)
        by ring,
      show ((k : ℚ) + j + 2 + k) * ((k : ℚ) + j + 2 + k - 1) * (2 * ((k : ℚ) + j + 2) - 2 * k - 1) =
        (2 * k + j + 2) * (2 * k + j + 1) * (2 * j + 3) by ring]
    have d1 : ((2 : ℚ) * k + j + 3) * (2 * k + j + 2) * (2 * j + 1) ≠ 0 := by positivity
    have d2 : ((2 : ℚ) * k + j + 2) * (2 * k + j + 1) * (2 * j + 3) ≠ 0 := by positivity
    have d7 : ((j : ℚ) + 1) * (k + j + 1) ≠ 0 := by positivity
    have d8 : ((j : ℚ) + 1 + 1) * (k + (j + 1) + 1) ≠ 0 := by positivity
    have d9 : 4 * ((k : ℚ) + 1) ^ 2 * (2 * (j + 1) + 1) ≠ 0 := by positivity
    field_simp
    ring
  -- the closed form
  let b : ℕ → ℕ := fun n => ∑ k ∈ range (n + 1), t k (n - k)
  have hrec : ∀ N : ℕ, 3 * ((N : ℚ) + 2) ^ 2 * (b (N + 2) : ℚ) =
      4 * (28 * ((N : ℚ) + 2) ^ 2 - 28 * ((N : ℚ) + 2) + 9) * (b (N + 1) : ℚ) -
        64 * (4 * ((N : ℚ) + 2) - 5) * (4 * ((N : ℚ) + 2) - 3) * (b N : ℚ) := by
    intro N
    have hb2 : (b (N + 2) : ℚ) = ∑ k ∈ range (N + 1), (t k (N - k + 2) : ℚ) +
        t (N + 1) 1 + t (N + 2) 0 := by
      simp only [b]
      rw [sum_range_succ, sum_range_succ, show N + 2 - (N + 1) = 1 by omega,
        show N + 2 - (N + 2) = 0 by omega]
      push_cast
      congr 2
      exact sum_congr rfl (fun k hk => by rw [mem_range] at hk; rw [show N + 2 - k = N - k + 2 by omega])
    have hb1 : (b (N + 1) : ℚ) = ∑ k ∈ range (N + 1), (t k (N - k + 1) : ℚ) + t (N + 1) 0 := by
      simp only [b]
      rw [sum_range_succ, show N + 1 - (N + 1) = 0 by omega]
      push_cast
      congr 1
      exact sum_congr rfl (fun k hk => by rw [mem_range] at hk; rw [show N + 1 - k = N - k + 1 by omega])
    have hb0 : (b N : ℚ) = ∑ k ∈ range (N + 1), (t k (N - k) : ℚ) := by
      simp only [b]; push_cast; rfl
    let G : ℕ → ℚ := fun k => (t k (N + 2 - k) : ℚ) * R ((N : ℚ) + 2) (k : ℚ)
    have hmid : ∀ k ∈ range (N + 1),
        3 * ((N : ℚ) + 2) ^ 2 * (t k (N - k + 2) : ℚ)
          - 4 * (28 * ((N : ℚ) + 2) ^ 2 - 28 * ((N : ℚ) + 2) + 9) * (t k (N - k + 1) : ℚ)
          + 64 * (4 * ((N : ℚ) + 2) - 5) * (4 * ((N : ℚ) + 2) - 3) * (t k (N - k) : ℚ)
        = G (k + 1) - G k := by
      intro k hk
      rw [mem_range] at hk
      obtain ⟨j, rfl⟩ : ∃ j, N = k + j := ⟨N - k, by omega⟩
      have e1 : k + j - k = j := by omega
      have e2 : k + j + 2 - (k + 1) = j + 1 := by omega
      have e3 : k + j + 2 - k = j + 2 := by omega
      simp only [G, e1, e2, e3]
      push_cast
      have h := mid k j
      rw [show (k : ℚ) + j + 2 = (k : ℚ) + (j : ℚ) + 2 by ring] at h
      linear_combination h
    have htel : ∑ k ∈ range (N + 1), (G (k + 1) - G k) = G (N + 1) - G 0 :=
      sum_range_sub G (N + 1)
    have hG0 : G 0 = 0 := by simp [G, R]
    have hbd : 3 * ((N : ℚ) + 2) ^ 2 * (t (N + 1) 1 : ℚ)
        - 4 * (28 * ((N : ℚ) + 2) ^ 2 - 28 * ((N : ℚ) + 2) + 9) * (t (N + 1) 0 : ℚ)
        + 3 * ((N : ℚ) + 2) ^ 2 * (t (N + 2) 0 : ℚ) + G (N + 1) = 0 := by
      have A := R1 (N + 1) 0
      have B := R3 (N + 1) 0
      simp only [zero_add, mul_zero, add_zero, mul_one, one_mul] at A B
      have A' : (t (N + 1) 1 : ℚ) * ((N : ℚ) + 1 + 1) = (t (N + 1) 0 : ℚ) * (8 * (2 * ((N : ℚ) + 1) + 1)) := by
        exact_mod_cast A
      have B' : (t (N + 1 + 1) 0 : ℚ) * (4 * ((N : ℚ) + 1 + 1) ^ 2) =
          (t (N + 1) 1 : ℚ) * ((2 * ((N : ℚ) + 1) + 1) * (2 * ((N : ℚ) + 1) + 2)) := by
        exact_mod_cast B
      have hA : (t (N + 1) 1 : ℚ) = (t (N + 1) 0 : ℚ) * (8 * (2 * ((N : ℚ) + 1) + 1)) / ((N : ℚ) + 1 + 1) := by
        rw [eq_div_iff (by positivity)]; exact A'
      have hB : (t (N + 2) 0 : ℚ) = (t (N + 1) 1 : ℚ) * ((2 * ((N : ℚ) + 1) + 1) * (2 * ((N : ℚ) + 1) + 2)) /
          (4 * ((N : ℚ) + 1 + 1) ^ 2) := by
        rw [eq_div_iff (by positivity)]; exact B'
      simp only [G, show N + 2 - (N + 1) = 1 by omega]
      rw [hB, hA]
      simp only [R]
      push_cast
      rw [show ((N : ℚ) + 2 + (N + 1)) * ((N : ℚ) + 2 + (N + 1) - 1) * (2 * ((N : ℚ) + 2) - 2 * (N + 1) - 1)
        = (2 * N + 3) * (2 * N + 2) * 1 by ring]
      have d1 : ((2 : ℚ) * N + 3) * (2 * N + 2) * 1 ≠ 0 := by positivity
      have d2 : ((N : ℚ) + 1 + 1) ≠ 0 := by positivity
      have d3 : 4 * ((N : ℚ) + 1 + 1) ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    have hsum := sum_congr rfl hmid
    rw [htel, hG0, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum] at hsum
    rw [hb2, hb1, hb0]
    linear_combination hsum + hbd
  -- Lucas' theorem at p = 3
  have lucas : ∀ N K : ℕ, (Nat.choose N K : ZMod 3) =
      (Nat.choose (N % 3) (K % 3) : ZMod 3) * (Nat.choose (N / 3) (K / 3) : ZMod 3) := by
    intro N K
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← Nat.cast_mul]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := N) (k := K) (p := 3))
  have cbL : ∀ a d : ℕ, d < 3 →
      (Nat.centralBinom (3 * a + d) : ZMod 3) = (Nat.centralBinom d : ZMod 3) * (Nat.centralBinom a : ZMod 3) := by
    intro a d hd
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose (d),
      Nat.centralBinom_eq_two_mul_choose a, lucas,
      show 2 * (3 * a + d) % 3 = 2 * d % 3 by omega, show 2 * (3 * a + d) / 3 = 2 * a + 2 * d / 3 by omega,
      show (3 * a + d) % 3 = d by omega, show (3 * a + d) / 3 = a by omega]
    interval_cases d
    · simp
    · simp
    · have z : (Nat.choose (2 * 2 % 3) 2 : ZMod 3) = 0 := by decide
      have z' : (Nat.choose (2 * 2) 2 : ZMod 3) = 0 := by decide
      rw [z, z', zero_mul, zero_mul]
  have small : ∀ s < 3, ∀ e < 3,
      ((2 * s + e) / 3 = 0 ∧ (2 * s + e) % 3 = 2 * s + e) ∨
      ((Nat.centralBinom s : ZMod 3) * (Nat.centralBinom e : ZMod 3) *
          (Nat.choose ((2 * s + e) % 3) s : ZMod 3) = 0 ∧
        (Nat.centralBinom s : ZMod 3) * (Nat.centralBinom e : ZMod 3) *
          (Nat.choose (2 * s + e) s : ZMod 3) = 0) := by decide
  have h4 : (4 : ZMod 3) = 1 := by decide
  have T3 : ∀ i a s e : ℕ, s < 3 → e < 3 →
      (t (3 * i + s) (3 * a + e) : ZMod 3) = (t s e : ZMod 3) * (t i a : ZMod 3) := by
    intro i a s e hs he
    simp only [t]
    push_cast
    rw [h4, one_pow, one_pow, one_pow, cbL i s hs, cbL a e he, lucas,
      show (2 * (3 * i + s) + (3 * a + e)) % 3 = (2 * s + e) % 3 by omega,
      show (2 * (3 * i + s) + (3 * a + e)) / 3 = 2 * i + a + (2 * s + e) / 3 by omega,
      show (3 * i + s) % 3 = s by omega, show (3 * i + s) / 3 = i by omega]
    rcases small s hs e he with ⟨q, r⟩ | ⟨z1, z2⟩
    · rw [q, r, add_zero]; ring
    · calc (Nat.centralBinom s : ZMod 3) * (Nat.centralBinom i : ZMod 3) *
            ((Nat.centralBinom e : ZMod 3) * (Nat.centralBinom a : ZMod 3)) *
            ((Nat.choose ((2 * s + e) % 3) s : ZMod 3) *
              (Nat.choose (2 * i + a + (2 * s + e) / 3) i : ZMod 3)) * 1
          = ((Nat.centralBinom s : ZMod 3) * (Nat.centralBinom e : ZMod 3) *
              (Nat.choose ((2 * s + e) % 3) s : ZMod 3)) *
            ((Nat.centralBinom i : ZMod 3) * (Nat.centralBinom a : ZMod 3) *
              (Nat.choose (2 * i + a + (2 * s + e) / 3) i : ZMod 3)) := by ring
        _ = 0 := by rw [z1, zero_mul]
        _ = ((Nat.centralBinom s : ZMod 3) * (Nat.centralBinom e : ZMod 3) *
              (Nat.choose (2 * s + e) s : ZMod 3)) *
            ((Nat.centralBinom i : ZMod 3) * (Nat.centralBinom a : ZMod 3) *
              (Nat.choose (2 * i + a) i : ZMod 3)) := by rw [z2, zero_mul]
        _ = _ := by ring
  -- each term of the closed form splits into its last base-3 digits and the rest
  have tz : ∀ r < 3, ∀ s < 3, r < s →
      ((Nat.centralBinom s * Nat.centralBinom (3 + r - s) * Nat.choose (2 * s + (3 + r - s)) s *
        4 ^ (3 + r - s) : ℕ) : ZMod 3) = 0 := by decide
  have term : ∀ m r k : ℕ, r < 3 → k ≤ 3 * m + r →
      (t k (3 * m + r - k) : ZMod 3) =
        if k % 3 ≤ r then (t (k % 3) (r - k % 3) : ZMod 3) * (t (k / 3) (m - k / 3) : ZMod 3)
        else 0 := by
    intro m r k hr hk
    have hs : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    by_cases h : k % 3 ≤ r
    · rw [if_pos h]
      have := T3 (k / 3) (m - k / 3) (k % 3) (r - k % 3) hs (by omega)
      rw [show 3 * (k / 3) + k % 3 = k by omega,
        show 3 * (m - k / 3) + (r - k % 3) = 3 * m + r - k by omega] at this
      exact this
    · rw [if_neg h]
      have := T3 (k / 3) (m - k / 3 - 1) (k % 3) (3 + r - k % 3) hs (by omega)
      rw [show 3 * (k / 3) + k % 3 = k by omega,
        show 3 * (m - k / 3 - 1) + (3 + r - k % 3) = 3 * m + r - k by omega] at this
      rw [this]
      have z : (t (k % 3) (3 + r - k % 3) : ZMod 3) = 0 := tz r hr (k % 3) hs (by omega)
      rw [z, zero_mul]
  -- the closed form is multiplicative modulo 3 in the base-3 digits
  have mult : ∀ m r : ℕ, r < 3 → (b (3 * m + r) : ZMod 3) = (b r : ZMod 3) * (b m : ZMod 3) := by
    intro m r hr
    let F : ℕ → ZMod 3 := fun k =>
      if k % 3 ≤ r then (t (k % 3) (r - k % 3) : ZMod 3) * (t (k / 3) (m - k / 3) : ZMod 3) else 0
    have hF0 : ∀ k, r < k % 3 → F k = 0 := fun k hk => if_neg (by omega)
    have h1 : (b (3 * m + r) : ZMod 3) = ∑ k ∈ range (3 * m + r + 1), F k := by
      simp only [b]
      push_cast
      exact sum_congr rfl (fun k hk => term m r k hr (by rw [mem_range] at hk; omega))
    have h2 : ∑ k ∈ range (3 * m + r + 1), F k = ∑ k ∈ range (3 * (m + 1)), F k := by
      interval_cases r
      · rw [show 3 * (m + 1) = 3 * m + 0 + 1 + 1 + 1 by ring, sum_range_succ _ (3 * m + 0 + 1 + 1),
          sum_range_succ _ (3 * m + 0 + 1), hF0 _ (by omega), hF0 _ (by omega)]
        simp
      · rw [show 3 * (m + 1) = 3 * m + 1 + 1 + 1 by ring, sum_range_succ _ (3 * m + 1 + 1),
          hF0 _ (by omega), add_zero]
      · rw [show 3 * (m + 1) = 3 * m + 2 + 1 by ring]
    have h3 : ∀ M : ℕ, ∑ k ∈ range (3 * M), F k =
        ∑ i ∈ range M, (F (3 * i) + F (3 * i + 1) + F (3 * i + 2)) := by
      intro M
      induction M with
      | zero => simp
      | succ M ih =>
        rw [show 3 * (M + 1) = 3 * M + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
          sum_range_succ, ih, sum_range_succ]
        ring
    have h4 : ∀ i : ℕ, F (3 * i) + F (3 * i + 1) + F (3 * i + 2) =
        (b r : ZMod 3) * (t i (m - i) : ZMod 3) := by
      intro i
      simp only [F, show (3 * i) % 3 = 0 by omega, show (3 * i + 1) % 3 = 1 by omega,
        show (3 * i + 2) % 3 = 2 by omega, show (3 * i) / 3 = i by omega,
        show (3 * i + 1) / 3 = i by omega, show (3 * i + 2) / 3 = i by omega, b]
      interval_cases r <;> simp [sum_range_succ] <;> ring
    rw [h1, h2, h3, sum_congr rfl (fun i _ => h4 i), ← mul_sum]
    congr 1
    simp only [b]
    push_cast
    rfl
  have b0 : (b 0 : ZMod 3) = 1 := by simp only [b, t]; decide
  have b1 : (b 1 : ZMod 3) = 0 := by simp only [b, t]; decide
  have b2 : (b 2 : ZMod 3) = 0 := by simp only [b, t]; decide
  have dvd3 : ∀ n, 0 < n → (b n : ZMod 3) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hm := mult (n / 3) (n % 3) (Nat.mod_lt _ (by norm_num))
      rw [show 3 * (n / 3) + n % 3 = n by omega] at hm
      rw [hm]
      rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
      · rw [h, b0, ih (n / 3) (by omega) (by omega), mul_zero]
      · rw [h, b1, zero_mul]
      · rw [h, b2, zero_mul]
  -- the recurrence determines a = b
  have ab : ∀ n, a n = (b n : ℚ) ∧ a (n + 1) = (b (n + 1) : ℚ) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [a, b, t]; norm_num
      · simp only [a, b, t]; norm_num [sum_range_succ, Nat.centralBinom, Nat.choose]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n + 1 + 1 = n + 2 from rfl]
      simp only [a]
      rw [ih.1, ih.2, div_eq_iff (by positivity)]
      linear_combination (-1 : ℚ) * hrec n
  intro n hn
  have h := dvd3 n hn
  rw [ZMod.natCast_eq_zero_iff] at h
  obtain ⟨q, hq⟩ := h
  refine ⟨q, ?_⟩
  rw [(ab n).1, hq]
  push_cast
  ring

end D5.S3.Quantum.Molecular.OctahedralPrecessionPeriods
