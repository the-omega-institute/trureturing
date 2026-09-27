/- GID: D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves R. J. Mathar's 2012 recurrence conjecture for OEIS A026023, the number of +-1 walks of length n on the nonnegative integers starting at 3 (walks of a random walker from x = 4 not yet adsorbed at x = 0): (n+4)(n-1)a(n) + (n-1)(n+1)a(n-1) - 2(n+1)(2n+1)a(n-2) - 4(n-1)(n+1)a(n-3) = 0 for n >= 3. -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the
  first-step bijection `split` (a walk of length n + 1 from x is `Fin.cons x` of a walk of
  length n from x + 1 or, when x >= 1, from x - 1) and the induction `count` identifying the
  walk count with the reflection count sum over d of C(n, d) for n < 2d + x + 2 and 2d <= n + x,
  which at x = 3 gives a(2m) = C(2m + 2, m) and a(2m + 1) = 2 C(2m + 2, m); the count is
  Theorem 2.1 of Jianu and Daus 2025, entering as a local step
admission_basis: open-problem-resolution (issue #10761)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.RandomWalks.SurvivingWalkRecurrence

open Finset

/-!
OEIS A026023 (Clark Kimberling): the number of sequences `s(0), s(1), ..., s(n)` of nonnegative
integers with `|s(i) - s(i - 1)| = 1` for `i = 1, ..., n` and `s(0) = 3`. R. M. Ziff (2014):
`a(n) / 2^n` is the probability that a random walker starting at `x = 4` and jumping `±1` with
equal probability is not adsorbed at the boundary `x = 0` at time `n`. R. J. Mathar (2012)
conjectured the order-3 recurrence stated in `claim`.
-/

/-- The sequences `s(0), ..., s(n)` of nonnegative integers with `s(0) = x` and
`|s(i) - s(i - 1)| = 1` for `i = 1, ..., n`. -/
def walks (n x : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {s | s 0 = x ∧ ∀ i : Fin n, s i.succ = s i.castSucc + 1 ∨ s i.succ + 1 = s i.castSucc}

/-- A026023: the number of such sequences with `s(0) = 3`. -/
noncomputable def a (n : ℕ) : ℕ := (walks n 3).ncard

/-- Mathar's conjecture (OEIS A026023, formula field, 2012). -/
def claim : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 4) * (n - 1) * a n + (n - 1) * (n + 1) * a (n - 1) -
      2 * (n + 1) * (2 * n + 1) * a (n - 2) - 4 * (n - 1) * (n + 1) * a (n - 3) = 0

theorem result : claim := by
  -- the first step splits a walk of length `n + 1` from `x` into a walk of length `n`
  -- from `x + 1` or, when `x ≥ 1`, from `x - 1`
  have split : ∀ n x : ℕ, walks (n + 1) x =
      (fun t : Fin (n + 1) → ℕ => (Fin.cons x t : Fin (n + 2) → ℕ)) ''
        (walks n (x + 1) ∪ {t | t ∈ walks n (x - 1) ∧ 1 ≤ x}) := by
    intro n x
    ext s
    simp only [walks, Set.mem_ofPred_eq, Set.mem_image, Set.mem_union]
    constructor
    · rintro ⟨h0, hs⟩
      refine ⟨Fin.tail s, ?_, ?_⟩
      · have hsteps : ∀ i : Fin n, Fin.tail s i.succ = Fin.tail s i.castSucc + 1 ∨
            Fin.tail s i.succ + 1 = Fin.tail s i.castSucc := by
          intro i
          have h := hs i.succ
          rw [← Fin.succ_castSucc] at h
          exact h
        have h1 := hs 0
        rw [Fin.castSucc_zero, h0] at h1
        change Fin.tail s 0 = x + 1 ∨ Fin.tail s 0 + 1 = x at h1
        rcases h1 with h | h
        · exact Or.inl ⟨h, hsteps⟩
        · exact Or.inr ⟨⟨by omega, hsteps⟩, by omega⟩
      · rw [← h0]
        exact Fin.cons_self_tail s
    · rintro ⟨t, ht, rfl⟩
      have ht' : (t 0 = x + 1 ∨ t 0 + 1 = x) ∧ ∀ i : Fin n,
          t i.succ = t i.castSucc + 1 ∨ t i.succ + 1 = t i.castSucc := by
        rcases ht with ⟨h0, hs⟩ | ⟨⟨h0, hs⟩, hx⟩
        · exact ⟨Or.inl h0, hs⟩
        · exact ⟨Or.inr (by omega), hs⟩
      refine ⟨Fin.cons_zero _ _, fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
        exact ht'.1
      · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact ht'.2 j
  -- the reflection count satisfies the same recursion (Pascal's rule)
  have pascal : ∀ n x : ℕ,
      (∑ d ∈ range (n + 2), if n + 1 < 2 * d + x + 2 ∧ 2 * d ≤ n + 1 + x
        then (n + 1).choose d else 0) =
      (∑ d ∈ range (n + 1), if n < 2 * d + (x + 1) + 2 ∧ 2 * d ≤ n + (x + 1)
        then n.choose d else 0) +
      if 1 ≤ x then
        ∑ d ∈ range (n + 1), if n < 2 * d + (x - 1) + 2 ∧ 2 * d ≤ n + (x - 1)
          then n.choose d else 0
      else 0 := by
    intro n x
    set g : ℕ → ℕ := fun d => if n + 1 < 2 * d + x + 2 ∧ 2 * d ≤ n + 1 + x then n.choose d else 0
      with hg
    have hlast : g (n + 1) = 0 := by simp [hg, Nat.choose_succ_self]
    have hshift : (∑ d ∈ range (n + 2), if n + 1 < 2 * d + x + 2 ∧ 2 * d ≤ n + 1 + x
        then (n + 1).choose d else 0) = (∑ d ∈ range (n + 1), if n + 1 < 2 * (d + 1) + x + 2 ∧
          2 * (d + 1) ≤ n + 1 + x then n.choose d else 0) + ∑ d ∈ range (n + 1), g d := by
      have h2 := sum_range_succ' g (n + 1)
      rw [sum_range_succ, hlast, add_zero] at h2
      rw [sum_range_succ', h2, ← add_assoc, ← sum_add_distrib]
      congr 1
      · refine sum_congr rfl (fun d _ => ?_)
        simp only [hg, Nat.choose_succ_succ']
        split_ifs <;> simp
      · simp [hg]
    rw [hshift, ← sum_add_distrib]
    have hite : (if 1 ≤ x then
        ∑ d ∈ range (n + 1), if n < 2 * d + (x - 1) + 2 ∧ 2 * d ≤ n + (x - 1) then n.choose d else 0
        else 0) = ∑ d ∈ range (n + 1),
          if 1 ≤ x ∧ n < 2 * d + (x - 1) + 2 ∧ 2 * d ≤ n + (x - 1) then n.choose d else 0 := by
      split_ifs with hx
      · simp [hx]
      · simp [hx]
    rw [hite, ← sum_add_distrib]
    refine sum_congr rfl (fun d _ => ?_)
    simp only [hg]
    split_ifs <;> omega
  -- the walk count equals the reflection count
  have count : ∀ n x : ℕ, (walks n x).Finite ∧ (walks n x).ncard =
      ∑ d ∈ range (n + 1), if n < 2 * d + x + 2 ∧ 2 * d ≤ n + x then n.choose d else 0 := by
    intro n
    induction n with
    | zero =>
      intro x
      have h : walks 0 x = {fun _ => x} := by
        ext s
        simp only [walks, Set.mem_ofPred_eq, Set.mem_singleton_iff, IsEmpty.forall_iff,
          and_true]
        constructor
        · intro h
          funext i
          rw [Fin.fin_one_eq_zero i, h]
        · rintro rfl
          rfl
      rw [h]
      refine ⟨Set.finite_singleton _, ?_⟩
      simp
    | succ n ih =>
      intro x
      have hinj : Function.Injective
          (fun t : Fin (n + 1) → ℕ => (Fin.cons x t : Fin (n + 2) → ℕ)) :=
        Fin.cons_right_injective (α := fun _ => ℕ) x
      have hsub : {t | t ∈ walks n (x - 1) ∧ 1 ≤ x} ⊆ walks n (x - 1) := fun t ht => ht.1
      have hfin : (walks n (x + 1) ∪ {t | t ∈ walks n (x - 1) ∧ 1 ≤ x}).Finite :=
        (ih (x + 1)).1.union ((ih (x - 1)).1.subset hsub)
      have hdisj : Disjoint (walks n (x + 1)) {t | t ∈ walks n (x - 1) ∧ 1 ≤ x} := by
        rw [Set.disjoint_left]
        rintro t ⟨h1, -⟩ ⟨⟨h2, -⟩, hx⟩
        omega
      rw [split n x, pascal n x]
      refine ⟨hfin.image _, ?_⟩
      rw [Set.ncard_image_of_injective _ hinj,
        Set.ncard_union_eq hdisj (ih (x + 1)).1 ((ih (x - 1)).1.subset hsub), (ih (x + 1)).2]
      congr 1
      by_cases hx : 1 ≤ x
      · simp only [hx, and_true, Set.ofPred_mem_eq, if_true]
        exact (ih (x - 1)).2
      · simp [hx]
  -- at `x = 3` the reflection count is four consecutive binomial coefficients
  have av : ∀ n, (a n : ℤ) = ∑ d ∈ range (n + 1),
      if n < 2 * d + 3 + 2 ∧ 2 * d ≤ n + 3 then (n.choose d : ℤ) else 0 := by
    intro n
    rw [a, (count n 3).2]
    push_cast
    rfl
  have even : ∀ j : ℕ, (a (2 * j + 4) : ℤ) = (2 * j + 6).choose (j + 2) := by
    intro j
    rw [av, ← sum_filter]
    have hset : (range (2 * j + 4 + 1)).filter
        (fun d => 2 * j + 4 < 2 * d + 3 + 2 ∧ 2 * d ≤ 2 * j + 4 + 3) =
        {j, j + 1, j + 2, j + 3} := by
      ext d
      simp only [mem_filter, mem_range, mem_insert, mem_singleton]
      omega
    rw [hset, sum_insert (by simp), sum_insert (by simp), sum_insert (by simp), sum_singleton]
    have p1 : (2 * j + 5).choose (j + 1) = (2 * j + 4).choose j + (2 * j + 4).choose (j + 1) :=
      Nat.choose_succ_succ' _ _
    have p2 : (2 * j + 5).choose (j + 3) =
        (2 * j + 4).choose (j + 2) + (2 * j + 4).choose (j + 3) := Nat.choose_succ_succ' _ _
    have p3 : (2 * j + 6).choose (j + 2) =
        (2 * j + 5).choose (j + 1) + (2 * j + 5).choose (j + 2) := Nat.choose_succ_succ' _ _
    have p4 : (2 * j + 5).choose (j + 3) = (2 * j + 5).choose (j + 2) :=
      Nat.choose_symm_of_eq_add (by omega)
    norm_cast
    omega
  have odd : ∀ j : ℕ, (a (2 * j + 5) : ℤ) = 2 * (2 * j + 6).choose (j + 2) := by
    intro j
    rw [av, ← sum_filter]
    have hset : (range (2 * j + 5 + 1)).filter
        (fun d => 2 * j + 5 < 2 * d + 3 + 2 ∧ 2 * d ≤ 2 * j + 5 + 3) =
        {j + 1, j + 2, j + 3, j + 4} := by
      ext d
      simp only [mem_filter, mem_range, mem_insert, mem_singleton]
      omega
    rw [hset, sum_insert (by simp), sum_insert (by simp), sum_insert (by simp), sum_singleton]
    have p1 : (2 * j + 6).choose (j + 2) =
        (2 * j + 5).choose (j + 1) + (2 * j + 5).choose (j + 2) := Nat.choose_succ_succ' _ _
    have p2 : (2 * j + 6).choose (j + 4) =
        (2 * j + 5).choose (j + 3) + (2 * j + 5).choose (j + 4) := Nat.choose_succ_succ' _ _
    have p3 : (2 * j + 6).choose (j + 4) = (2 * j + 6).choose (j + 2) :=
      Nat.choose_symm_of_eq_add (by omega)
    norm_cast
    omega
  have small : (a 0 : ℤ) = 1 ∧ (a 1 : ℤ) = 2 ∧ (a 2 : ℤ) = 4 ∧ (a 3 : ℤ) = 8 := by
    simp only [av]
    decide
  -- closed form: a(2m) = C(2m + 2, m) and a(2m + 1) = 2 C(2m + 2, m)
  have closed : ∀ m : ℕ, (a (2 * m) : ℤ) = (2 * m + 2).choose m ∧
      (a (2 * m + 1) : ℤ) = 2 * (2 * m + 2).choose m := by
    intro m
    match m with
    | 0 => exact ⟨small.1, small.2.1⟩
    | 1 => exact ⟨small.2.2.1, by simpa using small.2.2.2⟩
    | j + 2 =>
      refine ⟨?_, ?_⟩
      · rw [show 2 * (j + 2) = 2 * j + 4 by omega, even, show 2 * j + 4 + 2 = 2 * j + 6 by omega]
      · rw [show 2 * (j + 2) + 1 = 2 * j + 5 by omega, odd,
          show 2 * (j + 2) + 2 = 2 * j + 6 by omega]
  -- (m + 1)(m + 3) C(2m + 4, m + 1) = 2(m + 2)(2m + 3) C(2m + 2, m)
  have step : ∀ m : ℕ, ((m : ℤ) + 1) * (m + 3) * (2 * m + 4).choose (m + 1) =
      2 * (m + 2) * (2 * m + 3) * (2 * m + 2).choose m := by
    intro m
    have q1 := Nat.add_one_mul_choose_eq (2 * m + 2) m
    have q2 := Nat.choose_mul_succ_eq (2 * m + 3) (m + 1)
    rw [show 2 * m + 3 + 1 - (m + 1) = m + 3 by omega] at q2
    have q1' : ((2 * m + 2 + 1 : ℕ) : ℤ) * (2 * m + 2).choose m =
        ((2 * m + 2 + 1).choose (m + 1) : ℤ) * (m + 1) := by exact_mod_cast q1
    have q2' : ((2 * m + 3).choose (m + 1) : ℤ) * ((2 * m + 3 + 1 : ℕ) : ℤ) =
        ((2 * m + 3 + 1).choose (m + 1) : ℤ) * ((m + 3 : ℕ) : ℤ) := by exact_mod_cast q2
    push_cast at q1' q2'
    linear_combination (-(2 * (m : ℤ) + 4)) * q1' + (-((m : ℤ) + 1)) * q2'
  have vals : ∀ j : ℕ, (a (2 * j) : ℤ) = (2 * j + 2).choose j ∧
      (a (2 * j + 1) : ℤ) = 2 * (2 * j + 2).choose j ∧
      (a (2 * j + 2) : ℤ) = (2 * j + 4).choose (j + 1) ∧
      (a (2 * j + 3) : ℤ) = 2 * (2 * j + 4).choose (j + 1) := by
    intro j
    obtain ⟨h0, h1⟩ := closed j
    obtain ⟨h2, h3⟩ := closed (j + 1)
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, show 2 * j + 2 + 2 = 2 * j + 4 by omega] at h2 h3
    exact ⟨h0, h1, h2, h3⟩
  have steps : ∀ j : ℕ, ((j : ℤ) + 2) * (j + 4) * (2 * j + 6).choose (j + 2) =
      2 * (j + 3) * (2 * j + 5) * (2 * j + 4).choose (j + 1) := by
    intro j
    have h := step (j + 1)
    rw [show 2 * (j + 1) + 4 = 2 * j + 6 by omega, show j + 1 + 1 = j + 2 by omega,
      show 2 * (j + 1) + 2 = 2 * j + 4 by omega] at h
    push_cast at h
    linear_combination h
  intro n hn
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    obtain ⟨-, e3, e2, e1⟩ := vals j
    rw [show 2 * (j + 2) = 2 * j + 4 by omega, show 2 * j + 4 - 1 = 2 * j + 3 by omega,
      show 2 * j + 4 - 2 = 2 * j + 2 by omega, show 2 * j + 4 - 3 = 2 * j + 1 by omega,
      even j, e1, e2, e3]
    have r0 := step j
    have r1 := steps j
    have hj : ((j : ℤ) + 2) ≠ 0 := by positivity
    refine (mul_eq_zero.mp ?_).resolve_left hj
    push_cast
    linear_combination (2 * (2 * (j : ℤ) + 3)) * r1 + (4 * (2 * (j : ℤ) + 5)) * r0
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨e3, e2, e1, e0⟩ := vals j
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega, show 2 * j + 3 - 1 = 2 * j + 2 by omega,
      show 2 * j + 3 - 2 = 2 * j + 1 by omega, show 2 * j + 3 - 3 = 2 * j by omega,
      e0, e1, e2, e3]
    have r0 := step j
    push_cast
    linear_combination 12 * r0

end D5.S3.StatisticalMechanics.RandomWalks.SurvivingWalkRecurrence
