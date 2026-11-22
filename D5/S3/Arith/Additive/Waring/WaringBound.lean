/- GID: D5/S3/Arith/Additive/Waring/WaringBound
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringBound.lean#L1-L262
   Modified for this repository. Local imports use their D5 module paths.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringStatement

/-!
# Lower bounds for Waring's function `g(k)`: Euler's construction

`WaringStatement.lean` fixes the statement of Waring's theorem: for every `k ≥ 1`
there is `g` such that every natural number is a sum of at most `g` `k`-th
powers.  The least such `g` is traditionally written `g(k)`.

This file proves the classical **lower bound**

```text
g(k) ≥ 2^k + ⌊(3/2)^k⌋ − 2
```

due to Euler.  The witness is

```text
N = 2^k ⌊(3/2)^k⌋ − 1.
```

Since `N < 3^k`, every `k`-th power occurring in a representation of `N` is a
power of `0`, `1` or `2`.  Writing `t` for the number of `2^k` summands, one has
`t ≤ q − 1` where `q = ⌊(3/2)^k⌋`, and replacing each `2^k` by `2^k` ones shows
that at least `N − (q − 1)(2^k − 1) = 2^k + q − 2` summands are needed.

Together with Lagrange's four-square theorem this pins down `g(1) = 1` and
`g(2) = 4`, and it gives the first lower bounds `g(3) ≥ 9`, `g(4) ≥ 19`,
`g(5) ≥ 37`, `g(6) ≥ 73`.  The matching upper bounds are the content of the
Dickson–Pillai–Rubugunday–Niven theorem and are *not* proved here.
-/

open Finset

namespace Waring

/-- `g` is a Waring bound for exponent `k`: every natural number is a sum of at
most `g` nonnegative `k`-th powers. -/
def IsWaringBound (k g : ℕ) : Prop :=
  ∀ n : ℕ, ∃ s ≤ g, IsSumOfKthPowers k n s

/-- `WaringTheorem` says exactly that every `k ≥ 1` admits a Waring bound. -/
theorem waringTheorem_iff :
    WaringTheorem ↔ ∀ k : ℕ, 0 < k → ∃ g : ℕ, IsWaringBound k g := Iff.rfl

/-- `⌊(3/2)^k⌋`, written as the natural number `3^k / 2^k`. -/
def eulerQ (k : ℕ) : ℕ := 3 ^ k / 2 ^ k

theorem eulerQ_pos (k : ℕ) : 0 < eulerQ k := by
  have h2 : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hle : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
  exact Nat.div_pos hle h2

theorem eulerQ_mul_le (k : ℕ) : eulerQ k * 2 ^ k ≤ 3 ^ k :=
  Nat.div_mul_le_self _ _

/-! ## Euler's construction -/

/-- Euler's witness `N = 2^k ⌊(3/2)^k⌋ − 1` needs at least `2^k + ⌊(3/2)^k⌋ − 2`
`k`-th powers in every representation. -/
theorem euler_core (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, N < 3 ^ k ∧
      ∀ s : ℕ, IsSumOfKthPowers k N s → 2 ^ k + eulerQ k - 2 ≤ s := by
  classical
  have h2 : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hq : 0 < eulerQ k := eulerQ_pos k
  have hNlt : 2 ^ k * eulerQ k - 1 < 3 ^ k := by
    have hpos : 0 < 2 ^ k * eulerQ k := Nat.mul_pos h2 hq
    have hle : 2 ^ k * eulerQ k ≤ 3 ^ k := by
      rw [mul_comm]
      exact eulerQ_mul_le k
    omega
  refine ⟨2 ^ k * eulerQ k - 1, hNlt, ?_⟩
  intro s hs
  obtain ⟨f, hf⟩ := hs
  -- Every summand is at most `2^k`, because the total is `< 3^k`.
  have hle_sum : ∀ i : Fin s, (f i) ^ k ≤ 2 ^ k * eulerQ k - 1 := by
    intro i
    rw [hf]
    exact Finset.single_le_sum (f := fun i : Fin s => (f i) ^ k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hlt3 : ∀ i : Fin s, f i < 3 := by
    intro i
    have h1 : (f i) ^ k < 3 ^ k := lt_of_le_of_lt (hle_sum i) hNlt
    exact (Nat.pow_lt_pow_iff_left hk.ne').mp h1
  -- Split each summand according to whether the base is `2`, `1` or `0`.
  have hterm : ∀ i : Fin s,
      (f i) ^ k = (if f i = 2 then 2 ^ k else 0) + (if f i = 1 then 1 else 0) := by
    intro i
    have h' := hlt3 i
    interval_cases f i
    · rw [Nat.zero_pow hk]
      simp
    · simp
    · simp
  set A : Finset (Fin s) := Finset.univ.filter (fun i => f i = 2) with hA
  set B : Finset (Fin s) := Finset.univ.filter (fun i => f i = 1) with hB
  have hsum : (∑ i : Fin s, (f i) ^ k) = A.card * 2 ^ k + B.card := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
    have hA' : (∑ i : Fin s, if f i = 2 then 2 ^ k else 0) = A.card * 2 ^ k := by
      rw [← Finset.sum_filter, Finset.sum_const, hA, nsmul_eq_mul]
      simp
    have hB' : (∑ i : Fin s, if f i = 1 then 1 else 0) = B.card := by
      rw [← Finset.sum_filter, Finset.sum_const, hB, nsmul_eq_mul, mul_one]
      simp
    rw [hA', hB']
  have hN : 2 ^ k * eulerQ k - 1 = A.card * 2 ^ k + B.card := hf.trans hsum
  -- At most `q - 1` summands can be `2^k`.
  have hAcard_le : A.card * 2 ^ k ≤ 2 ^ k * eulerQ k - 1 := by
    rw [hN]
    exact Nat.le_add_right _ _
  have hAcard_lt : A.card * 2 ^ k < eulerQ k * 2 ^ k := by
    have hpos : 0 < 2 ^ k * eulerQ k := Nat.mul_pos h2 hq
    have h1 : A.card * 2 ^ k < 2 ^ k * eulerQ k :=
      lt_of_le_of_lt hAcard_le (Nat.sub_lt hpos one_pos)
    simpa [mul_comm] using h1
  have hAq' : A.card < eulerQ k := (Nat.mul_lt_mul_right h2).mp hAcard_lt
  have hAq : A.card ≤ eulerQ k - 1 := by omega
  -- The two filters are disjoint, so their total size is at most `s`.
  have hAB : A.card + B.card ≤ s := by
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      rw [hA] at hiA
      rw [hB] at hiB
      simp at hiA hiB
      omega
    have hsub : A ∪ B ⊆ Finset.univ := Finset.subset_univ _
    have hcard := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint hdisj, Finset.card_univ, Fintype.card_fin] at hcard
  -- Final arithmetic, carried out in `ℤ`.
  have hNz : ((2 ^ k * eulerQ k - 1 : ℕ) : ℤ) = (A.card : ℤ) * (2 : ℤ) ^ k + (B.card : ℤ) := by
    rw [hN]
    push_cast
    ring
  have hNz' : ((2 ^ k * eulerQ k - 1 : ℕ) : ℤ) + 1 = (2 : ℤ) ^ k * (eulerQ k : ℤ) := by
    have hpos : 0 < 2 ^ k * eulerQ k := Nat.mul_pos h2 hq
    have h1 : ((2 ^ k * eulerQ k - 1 : ℕ) : ℤ) = ((2 ^ k * eulerQ k : ℕ) : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ k * eulerQ k)]
      norm_num
    rw [h1]
    push_cast
    ring
  have hAqz : (A.card : ℤ) ≤ (eulerQ k : ℤ) - 1 := by
    have h1 : (A.card : ℤ) < (eulerQ k : ℤ) := by exact_mod_cast hAq'
    linarith
  have hABz : (A.card : ℤ) + (B.card : ℤ) ≤ (s : ℤ) := by exact_mod_cast hAB
  have hP1 : (0 : ℤ) ≤ (2 : ℤ) ^ k - 1 := by
    have h1 : (1 : ℤ) ≤ (2 : ℤ) ^ k := by
      have h := Nat.one_le_pow k 2 (by norm_num)
      exact_mod_cast h
    linarith
  have hmul : (A.card : ℤ) * ((2 : ℤ) ^ k - 1) ≤ ((eulerQ k : ℤ) - 1) * ((2 : ℤ) ^ k - 1) :=
    mul_le_mul_of_nonneg_right hAqz hP1
  have hgoalz : (2 : ℤ) ^ k + (eulerQ k : ℤ) - 2 ≤ (s : ℤ) := by
    nlinarith [hNz, hNz', hABz, hmul]
  -- Return to `ℕ`.
  have h2q : 2 ≤ 2 ^ k + eulerQ k := by
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have h2' : 1 ≤ eulerQ k := hq
    omega
  have hcast : ((2 ^ k + eulerQ k - 2 : ℕ) : ℤ) = (2 : ℤ) ^ k + (eulerQ k : ℤ) - 2 := by
    rw [Nat.cast_sub h2q]
    push_cast
    ring
  have : ((2 ^ k + eulerQ k - 2 : ℕ) : ℤ) ≤ (s : ℤ) := by
    rw [hcast]
    exact hgoalz
  exact_mod_cast this

/-- Euler's lower bound: `g(k) ≥ 2^k + ⌊(3/2)^k⌋ − 2` for every `k ≥ 1`. -/
theorem euler_lower_bound (k : ℕ) (hk : 0 < k) {g : ℕ} (hg : IsWaringBound k g) :
    2 ^ k + eulerQ k - 2 ≤ g := by
  obtain ⟨N, -, hN⟩ := euler_core k hk
  obtain ⟨s, hs, hrepr⟩ := hg N
  exact le_trans (hN s hrepr) hs

/-! ## Exact values `g(1) = 1` and `g(2) = 4` -/

theorem isWaringBound_one : IsWaringBound 1 1 := by
  intro n
  exact ⟨1, le_rfl, ⟨fun _ => n, by simp⟩⟩

/-- Lagrange's four-square theorem gives `g(2) ≤ 4`. -/
theorem isWaringBound_two : IsWaringBound 2 4 := by
  intro n
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  refine ⟨4, le_rfl, ⟨![a, b, c, d], ?_⟩⟩
  simp [Fin.sum_univ_four, h]

/-- `7` is not a sum of three squares. -/
theorem seven_not_three_squares (a b c : ℕ) : a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by
  intro h
  have ha : a < 3 := by nlinarith
  have hb : b < 3 := by nlinarith
  have hc : c < 3 := by nlinarith
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega

/-- A finite sum of at most three squares is a sum of three squares. -/
theorem eq_three_squares_of_sum_fin_le_three {s : ℕ} (hs : s ≤ 3) (f : Fin s → ℕ) :
    ∃ a b c : ℕ, (∑ i : Fin s, (f i) ^ 2) = a ^ 2 + b ^ 2 + c ^ 2 := by
  interval_cases s
  · exact ⟨0, 0, 0, by simp⟩
  · exact ⟨f 0, 0, 0, by simp⟩
  · exact ⟨f 0, f 1, 0, by simp [Fin.sum_univ_two]⟩
  · exact ⟨f 0, f 1, f 2, by simp [Fin.sum_univ_three]⟩

/-- `g(2) ≥ 4`: the number `7` needs four squares. -/
theorem four_le_of_isWaringBound_two (g : ℕ) (hg : IsWaringBound 2 g) : 4 ≤ g := by
  obtain ⟨s, hs, f, hf⟩ := hg 7
  by_contra h
  have hs3 : s ≤ 3 := by omega
  obtain ⟨a, b, c, habc⟩ := eq_three_squares_of_sum_fin_le_three hs3 f
  exact seven_not_three_squares a b c (by rw [← habc]; exact hf.symm)

/-- `g(1) = 1`. -/
theorem g_one_exact : IsWaringBound 1 1 ∧ ∀ g : ℕ, IsWaringBound 1 g → 1 ≤ g :=
  ⟨isWaringBound_one, fun g hg => by
    have h := euler_lower_bound 1 (by norm_num) hg
    norm_num [eulerQ] at h
    exact h⟩

/-- `g(2) = 4`, from Lagrange's theorem and Euler's construction. -/
theorem g_two_exact : IsWaringBound 2 4 ∧ ∀ g : ℕ, IsWaringBound 2 g → 4 ≤ g :=
  ⟨isWaringBound_two, fun g => four_le_of_isWaringBound_two g⟩

/-! ## Lower bounds for `g(3)`, `g(4)`, `g(5)`, `g(6)` -/

theorem g_three_ge (g : ℕ) (hg : IsWaringBound 3 g) : 9 ≤ g := by
  have h := euler_lower_bound 3 (by norm_num) hg
  norm_num [eulerQ] at h
  exact h

theorem g_four_ge (g : ℕ) (hg : IsWaringBound 4 g) : 19 ≤ g := by
  have h := euler_lower_bound 4 (by norm_num) hg
  norm_num [eulerQ] at h
  exact h

theorem g_five_ge (g : ℕ) (hg : IsWaringBound 5 g) : 37 ≤ g := by
  have h := euler_lower_bound 5 (by norm_num) hg
  norm_num [eulerQ] at h
  exact h

theorem g_six_ge (g : ℕ) (hg : IsWaringBound 6 g) : 73 ≤ g := by
  have h := euler_lower_bound 6 (by norm_num) hg
  norm_num [eulerQ] at h
  exact h

/-- The table of lower bounds proved in this file. -/
theorem g_lower_bounds :
    (∀ g : ℕ, IsWaringBound 3 g → 9 ≤ g) ∧
    (∀ g : ℕ, IsWaringBound 4 g → 19 ≤ g) ∧
    (∀ g : ℕ, IsWaringBound 5 g → 37 ≤ g) ∧
    (∀ g : ℕ, IsWaringBound 6 g → 73 ≤ g) :=
  ⟨fun g => g_three_ge g, fun g => g_four_ge g, fun g => g_five_ge g, fun g => g_six_ge g⟩

end Waring
