/- GID: D5/S3/Combinatorics/Circle/Orbit/TernaryPhaseZeroCount
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/Orbit/TernaryPhaseZeroCount
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Basic, mathlib/module/Mathlib.Data.Finset.SymmDiff]
   utility: none
   digest: Negative-label complementation counts all exact-zero subsets of ternary physical labels. -/
module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Exact zero-subset count for ternary physical labels

All subsets are finsets of the original labels `Fin n`; equal integer values
at different labels remain distinct choices. The only hypothesis is that
each value is -1, 0, or 1. In particular, no full-sum-zero hypothesis or
balance of positive and negative label counts is required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.TernaryPhaseZeroCount

open scoped BigOperators symmDiff

/-- Toggling the negative labels turns the signed sum into an ordinary
nonzero-label cardinality minus the total negative-label cardinality. -/
private theorem sum_eq_toggle_card {n : ℕ} (u : Fin n → ℤ)
    (hu : ∀ i, u i = -1 ∨ u i = 0 ∨ u i = 1) (A : Finset (Fin n)) :
    (∑ i ∈ A, u i) =
      ((((A ∆ (Finset.univ.filter (fun i => u i = -1))).filter
        (fun i => u i ≠ 0)).card : ℤ) -
        ((Finset.univ.filter (fun i => u i = -1)).card : ℤ)) := by
  classical
  let N : Finset (Fin n) := Finset.univ.filter (fun i => u i = -1)
  let T := (A ∆ N).filter (fun i => u i ≠ 0)
  have hpoint (i : Fin n) :
      (if i ∈ A then u i else 0) =
        (if i ∈ T then (1 : ℤ) else 0) -
          (if i ∈ N then (1 : ℤ) else 0) := by
    rcases hu i with hi | hi | hi <;>
      by_cases hA : i ∈ A <;>
      simp [T, N, Finset.mem_symmDiff, hi, hA]
  have hsum :
      (∑ i : Fin n, if i ∈ A then u i else 0) =
        ∑ i : Fin n, ((if i ∈ T then (1 : ℤ) else 0) -
          (if i ∈ N then (1 : ℤ) else 0)) :=
    Finset.sum_congr rfl (fun i _ => hpoint i)
  change (∑ i ∈ A, u i) = (T.card : ℤ) - (N.card : ℤ)
  simpa [Finset.sum_sub_distrib] using hsum

/-- A subset with exactly `r` nonzero labels is a pair consisting of an
arbitrary zero-label subset and an `r`-element nonzero-label subset. -/
private theorem card_filter_nonzero {n : ℕ} (u : Fin n → ℤ) (r : ℕ) :
    (Finset.univ.filter (fun A : Finset (Fin n) =>
      (A.filter (fun i => u i ≠ 0)).card = r)).card =
      2 ^ (Finset.univ.filter (fun i => u i = 0)).card *
        Nat.choose (Finset.univ.filter (fun i => u i ≠ 0)).card r := by
  classical
  let Z : Finset (Fin n) := Finset.univ.filter (fun i => u i = 0)
  let S : Finset (Fin n) := Finset.univ.filter (fun i => u i ≠ 0)
  let f := fun A : Finset (Fin n) =>
    (A.filter (fun i => u i = 0), A.filter (fun i => u i ≠ 0))
  let g := fun BC : Finset (Fin n) × Finset (Fin n) => BC.1 ∪ BC.2
  have hparts (B C : Finset (Fin n)) (hB : B ⊆ Z) (hC : C ⊆ S) :
      ((B ∪ C).filter (fun i => u i = 0),
        (B ∪ C).filter (fun i => u i ≠ 0)) = (B, C) := by
    have hB0 (i : Fin n) (hi : i ∈ B) : u i = 0 :=
      (Finset.mem_filter.mp (hB hi)).2
    have hC0 (i : Fin n) (hi : i ∈ C) : u i ≠ 0 :=
      (Finset.mem_filter.mp (hC hi)).2
    apply Prod.ext
    · apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hi, hz⟩
        exact hi.resolve_right (fun h => hC0 i h hz)
      · intro hi
        exact ⟨Or.inl hi, hB0 i hi⟩
    · apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hi, hnz⟩
        exact hi.resolve_left (fun h => hnz (hB0 i h))
      · intro hi
        exact ⟨Or.inr hi, hC0 i hi⟩
  have hcount :
      (Finset.univ.filter (fun A : Finset (Fin n) =>
        (A.filter (fun i => u i ≠ 0)).card = r)).card =
          (Z.powerset ×ˢ S.powersetCard r).card := by
    refine Finset.card_nbij' f g ?_ ?_ ?_ ?_
    · intro A hA
      have hcard := (Finset.mem_filter.mp hA).2
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_powerset.mpr ?_,
        Finset.mem_powersetCard.mpr ⟨?_, hcard⟩⟩
      · intro i hi
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
      · intro i hi
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · rintro ⟨B, C⟩ hBC
      obtain ⟨hB, hC⟩ := Finset.mem_product.mp hBC
      obtain ⟨hCS, hCr⟩ := Finset.mem_powersetCard.mp hC
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change ((B ∪ C).filter (fun i => u i ≠ 0)).card = r
      have hc := congrArg (fun BC : Finset (Fin n) × Finset (Fin n) => BC.2.card)
        (hparts B C (Finset.mem_powerset.mp hB) hCS)
      exact hc.trans hCr
    · intro A _
      change A.filter (fun i => u i = 0) ∪ A.filter (fun i => u i ≠ 0) = A
      apply Finset.ext
      intro i
      by_cases hi : u i = 0 <;> simp [hi]
    · rintro ⟨B, C⟩ hBC
      obtain ⟨hB, hC⟩ := Finset.mem_product.mp hBC
      exact hparts B C (Finset.mem_powerset.mp hB)
        (Finset.mem_powersetCard.mp hC).1
  simpa only [Finset.card_product, Finset.card_powerset,
    Finset.card_powersetCard, Z, S] using hcount

/-- Exact physical-label zero-subset count for every ternary integer source.
The three counts on the right are literally the numbers of zero, positive,
and negative labels. Empty domains, all-zero sources, and either missing
sign are included. -/
theorem zero_subsets_card (n : ℕ) (u : Fin n → ℤ)
    (hu : ∀ i, u i = -1 ∨ u i = 0 ∨ u i = 1) :
    (Finset.univ.filter (fun A : Finset (Fin n) => (∑ i ∈ A, u i) = 0)).card =
      2 ^ (Finset.univ.filter (fun i => u i = 0)).card *
        Nat.choose
          ((Finset.univ.filter (fun i => u i = 1)).card +
            (Finset.univ.filter (fun i => u i = -1)).card)
          (Finset.univ.filter (fun i => u i = 1)).card := by
  classical
  let P : Finset (Fin n) := Finset.univ.filter (fun i => u i = 1)
  let N : Finset (Fin n) := Finset.univ.filter (fun i => u i = -1)
  let S : Finset (Fin n) := Finset.univ.filter (fun i => u i ≠ 0)
  have hzero (A : Finset (Fin n)) :
      (∑ i ∈ A, u i) = 0 ↔
        ((A ∆ N).filter (fun i => u i ≠ 0)).card = N.card := by
    rw [sum_eq_toggle_card u hu A, sub_eq_zero]
    exact Nat.cast_inj
  have htoggle :
      (Finset.univ.filter (fun A : Finset (Fin n) => (∑ i ∈ A, u i) = 0)).card =
        (Finset.univ.filter (fun B : Finset (Fin n) =>
          (B.filter (fun i => u i ≠ 0)).card = N.card)).card := by
    refine Finset.card_nbij' (fun A => A ∆ N) (fun B => B ∆ N) ?_ ?_ ?_ ?_
    · intro A hA
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hzero A).mp (Finset.mem_filter.mp hA).2⟩
    · intro B hB
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (hzero (B ∆ N)).mpr ?_⟩
      simpa only [symmDiff_symmDiff_cancel_right] using (Finset.mem_filter.mp hB).2
    · intro A _
      simp only [symmDiff_symmDiff_cancel_right]
    · intro B _
      simp only [symmDiff_symmDiff_cancel_right]
  have hS : S = P ∪ N := by
    apply Finset.ext
    intro i
    simp only [S, P, N, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rcases hu i with hi | hi | hi <;> simp [hi]
  have hPN : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiN
    have hp : u i = 1 := (Finset.mem_filter.mp hiP).2
    have hn : u i = -1 := (Finset.mem_filter.mp hiN).2
    simp [hp] at hn
  have hScard : S.card = P.card + N.card := by
    rw [hS, Finset.card_union_of_disjoint hPN]
  calc
    _ = (Finset.univ.filter (fun B : Finset (Fin n) =>
        (B.filter (fun i => u i ≠ 0)).card = N.card)).card := htoggle
    _ = 2 ^ (Finset.univ.filter (fun i => u i = 0)).card *
        Nat.choose S.card N.card := card_filter_nonzero u N.card
    _ = 2 ^ (Finset.univ.filter (fun i => u i = 0)).card *
        Nat.choose (P.card + N.card) P.card := by
      rw [hScard, ← Nat.choose_symm_add]

end D5.S3.Combinatorics.Circle.TernaryPhaseZeroCount
