/- GID: D5/S1/FixedPoints/FiniteRepairTermination
   generality: G
   mirror-B: D5/B/S1/FixedPoints/FiniteRepairTermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict refinements of a finite equivalence partition terminate within the class-count gap. -/

import Mathlib.Data.Set.Card
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Order.Partition.Finpartition

/- Library-search audit trail (2026-08-21):
   * `rg` searches in `D5/` for strict refinement, equivalence relations,
     finite stabilization, and class counts found the related generic theorem
     `finite_monotone_iteration_reaches_fixed_point`, but no theorem with the
     sharp difference between the carrier size and the initial class count.
   * `rg` searches in pinned Mathlib for `Finpartition`, `card_mono`,
     `card_parts_le_card`, and antitone chains found the exact reusable
     ingredients `Finpartition.card_mono`, `Finpartition.card_parts_le_card`,
     and `WellFoundedLT.antitone_chain_condition`.
   * Pinned Mathlib has no exact theorem combining eventual stabilization of
     finite partitions with the sharp strict-change count, so only the missing
     cardinal bookkeeping is proved locally below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.FixedPoints.FiniteRepairTermination

open Finset

/-- A proper refinement of a finite partition has strictly more parts. -/
private theorem card_parts_lt_of_lt
    {X : Type*} [DecidableEq X] {s : Finset X}
    {P Q : Finpartition s} (h : P < Q) :
    #Q.parts < #P.parts := by
  classical
  let containingPart : P.parts → Q.parts := fun p =>
    ⟨Classical.choose (h.le p.property),
      (Classical.choose_spec (h.le p.property)).1⟩
  have containingPart_le (p : P.parts) :
      p.1 ⊆ (containingPart p).1 :=
    (Classical.choose_spec (h.le p.property)).2
  have containingPart_eq_of_le (p : P.parts) (q : Q.parts)
      (hpq : p.1 ⊆ q.1) : containingPart p = q := by
    apply Subtype.ext
    by_contra hne
    have hdisjoint : Disjoint (containingPart p).1 q.1 :=
      Q.disjoint (containingPart p).property q.property hne
    exact P.ne_bot p.property
      (disjoint_self.mp (hdisjoint.mono (containingPart_le p) hpq))
  have containingPart_surjective : Function.Surjective containingPart := by
    intro q
    obtain ⟨p, hp, hpq⟩ := Finpartition.exists_le_of_le h.le q.property
    exact ⟨⟨p, hp⟩, containingPart_eq_of_le ⟨p, hp⟩ q hpq⟩
  refine (Finpartition.card_mono h.le).lt_of_ne ?_
  intro cardsEqual
  have subtypeCardsEqual : Fintype.card P.parts = Fintype.card Q.parts := by
    simpa using cardsEqual.symm
  have containingPart_injective : Function.Injective containingPart :=
    ((Fintype.bijective_iff_surjective_and_card containingPart).2
      ⟨containingPart_surjective, subtypeCardsEqual⟩).1
  have hreverse : Q ≤ P := by
    intro q hq
    obtain ⟨p, hp, hpq⟩ := Finpartition.exists_le_of_le h.le hq
    refine ⟨p, hp, ?_⟩
    intro x hxq
    obtain ⟨p', hp', hxp'⟩ := P.exists_mem (Q.le hq hxq)
    have containingPart_p'_eq : containingPart ⟨p', hp'⟩ = ⟨q, hq⟩ := by
      apply Subtype.ext
      by_contra hne
      have hdisjoint : Disjoint (containingPart ⟨p', hp'⟩).1 q :=
        Q.disjoint (containingPart ⟨p', hp'⟩).property hq hne
      exact (Finset.disjoint_left.mp hdisjoint)
        (containingPart_le ⟨p', hp'⟩ hxp') hxq
    have containingPart_p_eq : containingPart ⟨p, hp⟩ = ⟨q, hq⟩ :=
      containingPart_eq_of_le ⟨p, hp⟩ ⟨q, hq⟩ hpq
    have pp' : (⟨p', hp'⟩ : P.parts) = ⟨p, hp⟩ :=
      containingPart_injective (containingPart_p'_eq.trans containingPart_p_eq.symm)
    have pp'_value : p' = p := congrArg Subtype.val pp'
    simpa [pp'_value] using hxp'
  exact h.ne (le_antisymm h.le hreverse)

/-- A sequence of equivalence partitions of a finite carrier which only
refines can make at most `|X| - initialClasses` strict changes; after its last
strict change the sequence is constant. -/
theorem finite_strict_repairs_stabilize
    {X : Type*} [Fintype X] [DecidableEq X]
    (partition : ℕ → Finpartition (Finset.univ : Finset X))
    (refines : ∀ n : ℕ, partition (n + 1) ≤ partition n) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → partition n = partition N) ∧
      {n : ℕ | partition (n + 1) ≠ partition n}.ncard ≤
        Fintype.card X - #(partition 0).parts := by
  let classCount : ℕ → ℕ := fun n => #(partition n).parts
  let changes : Set ℕ := {n | partition (n + 1) ≠ partition n}
  have partition_antitone : Antitone partition :=
    antitone_nat_of_succ_le refines
  have classCount_monotone : Monotone classCount := by
    intro m n hmn
    exact Finpartition.card_mono (partition_antitone hmn)
  have classCount_strict (n : ℕ) (hn : n ∈ changes) :
      classCount n < classCount (n + 1) := by
    apply card_parts_lt_of_lt
    exact (refines n).lt_of_ne hn
  let nextClassCount : ℕ → ℕ := fun n => classCount (n + 1)
  have nextClassCount_injective : Set.InjOn nextClassCount changes := by
    intro m hm n hn heq
    rcases lt_trichotomy m n with hmn | hmn | hnm
    · have hlt : nextClassCount m < nextClassCount n := by
        exact (classCount_monotone (Nat.succ_le_of_lt hmn)).trans_lt
          (classCount_strict n hn)
      exact (hlt.ne heq).elim
    · exact hmn
    · have hlt : nextClassCount n < nextClassCount m := by
        exact (classCount_monotone (Nat.succ_le_of_lt hnm)).trans_lt
          (classCount_strict m hm)
      exact (hlt.ne heq.symm).elim
  have nextClassCount_image_subset :
      nextClassCount '' changes ⊆ Set.Ioc (classCount 0) (Fintype.card X) := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (classCount_monotone (Nat.zero_le n)).trans_lt
        (classCount_strict n hn)
    · exact Finpartition.card_parts_le_card (partition (n + 1))
  have nextClassCount_image_finite : (nextClassCount '' changes).Finite :=
    (Set.finite_Ioc (classCount 0) (Fintype.card X)).subset
      nextClassCount_image_subset
  have changes_finite : changes.Finite :=
    Set.Finite.of_finite_image nextClassCount_image_finite
      nextClassCount_injective
  obtain ⟨N, stable⟩ :=
    WellFoundedLT.antitone_chain_condition partition_antitone
  constructor
  · exact ⟨N, fun n hn => (stable n hn).symm⟩
  · change changes.ncard ≤ Fintype.card X - classCount 0
    calc
      changes.ncard = (nextClassCount '' changes).ncard :=
        nextClassCount_injective.ncard_image.symm
      _ ≤ (Set.Ioc (classCount 0) (Fintype.card X)).ncard :=
        Set.ncard_le_ncard nextClassCount_image_subset
          (Set.finite_Ioc (classCount 0) (Fintype.card X))
      _ = Fintype.card X - classCount 0 := Set.ncard_Ioc_nat _ _

/-- At cutoff `n`, natural numbers below `n` are separate classes and all
numbers at least `n` form one tail class. -/
def cutoffSetoid (n : ℕ) : Setoid ℕ :=
  Setoid.ker (fun x => min x n)

/-- Moving the cutoff one step right strictly refines the tail equivalence
relation, producing an infinite strict refinement tower on `ℕ`. -/
theorem cutoffSetoid_strict_refines (n : ℕ) :
    cutoffSetoid (n + 1) < cutoffSetoid n := by
  constructor
  · intro a b hab
    change min a (n + 1) = min b (n + 1) at hab
    change min a n = min b n
    have h := congrArg (fun z : ℕ => min z n) hab
    simpa [min_assoc] using h
  · intro hreverse
    have hrel : cutoffSetoid n n (n + 1) := by
      change min n n = min (n + 1) n
      omega
    have h := hreverse hrel
    change min n (n + 1) = min (n + 1) (n + 1) at h
    omega

/-- Finite strict repair sequences stabilize within the available class-count
gap, while the natural-number cutoff relations witness that the finiteness
hypothesis cannot be dropped. -/
theorem finite_repair_termination_and_infinite_tower :
    (∀ (X : Type*) [Fintype X] [DecidableEq X]
        (partition : ℕ → Finpartition (Finset.univ : Finset X)),
        (∀ n : ℕ, partition (n + 1) ≤ partition n) →
        (∃ N : ℕ, ∀ n : ℕ, N ≤ n → partition n = partition N) ∧
          {n : ℕ | partition (n + 1) ≠ partition n}.ncard ≤
            Fintype.card X - #(partition 0).parts) ∧
      (∃ tower : ℕ → Setoid ℕ, ∀ n : ℕ, tower (n + 1) < tower n) := by
  constructor
  · intro X _ _ partition refines
    exact finite_strict_repairs_stabilize partition refines
  · exact ⟨cutoffSetoid, cutoffSetoid_strict_refines⟩

#print axioms finite_repair_termination_and_infinite_tower

end D5.S1.FixedPoints.FiniteRepairTermination
