/- GID: D5/S3/StatisticalMechanics/RandomWalks/WalkCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity
   mirror-E: none(waiver:general-reflection-count)
   anchors: []
   utility: none
   digest: Counts nonnegative unit-step walks from every natural height by reflection induction. -/
/-
proof_shape: walk_count: content
escape_witness: form (2): walk_count itself, through the first-step decomposition,
  disjoint finite image count and induction identifying the reflection sum.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
The family parameter and its defining equation accept the existing
SurvivingWalkRecurrence.walks without introducing another walk definition.
The result is an unbounded structural counting theorem, not finite enumeration,
checker infrastructure, numerical reduction or a certified finite instance.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.RandomWalks.WalkCount

open Finset

/-- Reflection count for a family with the nonnegative unit-step walk equation. -/
theorem walk_count
    (walks : (n : ℕ) → ℕ → Set (Fin (n + 1) → ℕ))
    (hwalks : ∀ n x : ℕ, walks n x =
      {s | s 0 = x ∧ ∀ i : Fin n,
        s i.succ = s i.castSucc + 1 ∨ s i.succ + 1 = s i.castSucc})
    (n x : ℕ) : (walks n x).Finite ∧ (walks n x).ncard =
      ∑ d ∈ range (n + 1), if n < 2*d+x+2 ∧ 2*d ≤ n+x then n.choose d else 0 := by
  have split : ∀ n x : ℕ, walks (n + 1) x =
      (fun t : Fin (n + 1) → ℕ => (Fin.cons x t : Fin (n + 2) → ℕ)) ''
        (walks n (x + 1) ∪ {t | t ∈ walks n (x - 1) ∧ 1 ≤ x}) := by
    intro n x
    ext s
    simp only [hwalks, Set.mem_ofPred_eq, Set.mem_image, Set.mem_union]
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
        simp only [hwalks, Set.mem_ofPred_eq, Set.mem_singleton_iff, IsEmpty.forall_iff,
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
        rintro t ht₁ ⟨ht₂, hx⟩
        rw [hwalks] at ht₁ ht₂
        have h1 := ht₁.1
        have h2 := ht₂.1
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
  exact count n x

end D5.S3.StatisticalMechanics.RandomWalks.WalkCount
