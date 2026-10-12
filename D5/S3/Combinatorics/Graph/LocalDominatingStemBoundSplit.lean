/- GID: D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit
   mirror-E: none(waiver:finite-combinatorial-identities)
   anchors: []
   utility: none
   digest: Dominating sets containing a stem split into free leaf choices and partial residual domination. -/

import D5.S3.Combinatorics.Graph.LocalDominatingStemBoundStructure
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LocalDominatingStemBoundSplit

open Finset DominatingSetAverage LocalDominatingStemBoundStructure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The forward map joining the three disjoint parts. -/
noncomputable def joinStem (v : V) (p : Finset V × Finset V) : Finset V :=
  insert v (p.1 ∪ p.2)

theorem leaf_not_self (G : SimpleGraph V) (v : V) : v ∉ leafNeighbors G v := by
  classical
  simp

theorem split_intersections {G : SimpleGraph V} (v : V) (K T : Finset V)
    (hK : K ⊆ leafNeighbors G v) (hT : T ⊆ remaining G v) :
    joinStem v (K,T) ∩ leafNeighbors G v = K ∧
      joinStem v (K,T) ∩ remaining G v = T := by
  classical
  have hvL := leaf_not_self G v
  have hvR : v ∉ remaining G v := by simp
  have hdis : Disjoint (leafNeighbors G v) (remaining G v) := by
    apply disjoint_left.mpr
    intro x hx hr
    exact (mem_remaining.mp hr).2 (mem_leafNeighbors.mp hx)
  constructor <;> ext x <;> simp only [joinStem, mem_inter, mem_insert, mem_union,
    Prod.fst, Prod.snd]
  · constructor
    · rintro ⟨rfl | hx | hx, hl⟩
      · exact False.elim (hvL hl)
      · exact hx
      · exact False.elim (disjoint_left.mp hdis hl (hT hx))
    · intro hx
      exact ⟨Or.inr (Or.inl hx), hK hx⟩
  · constructor
    · rintro ⟨rfl | hx | hx, hr⟩
      · exact False.elim (hvR hr)
      · exact False.elim (disjoint_left.mp hdis (hK hx) hr)
      · exact hx
    · intro hx
      exact ⟨Or.inr (Or.inr hx), hT hx⟩

theorem split_reconstruct {G : SimpleGraph V} (v : V) (S : Finset V) (hv : v ∈ S) :
    joinStem v (S ∩ leafNeighbors G v, S ∩ remaining G v) = S := by
  classical
  ext x
  simp only [joinStem, mem_insert, mem_union, mem_inter, Prod.fst, Prod.snd]
  constructor
  · rintro (rfl | ⟨hx, _⟩ | ⟨hx, _⟩)
    · exact hv
    · exact hx
    · exact hx
  · intro hx
    by_cases hxv : x = v
    · exact Or.inl hxv
    by_cases hxL : x ∈ leafNeighbors G v
    · exact Or.inr (Or.inl ⟨hx, hxL⟩)
    · exact Or.inr (Or.inr ⟨hx, mem_remaining.mpr ⟨hxv, by simpa using hxL⟩⟩)

theorem joinStem_card {G : SimpleGraph V} (v : V) (K T : Finset V)
    (hK : K ⊆ leafNeighbors G v) (hT : T ⊆ remaining G v) :
    (joinStem v (K,T)).card = 1 + K.card + T.card := by
  classical
  have hv : v ∉ K ∪ T := by
    simp only [mem_union, not_or]
    exact ⟨fun h => leaf_not_self G v (hK h), fun h => (mem_remaining.mp (hT h)).1 rfl⟩
  have hd : Disjoint K T := by
    apply disjoint_left.mpr
    intro x hx hxt
    exact (mem_remaining.mp (hT hxt)).2 (mem_leafNeighbors.mp (hK hx))
  rw [joinStem, card_insert_of_notMem hv, card_union_of_disjoint hd]
  omega

theorem stem_family_card (G : SimpleGraph V) (v : V) :
    (domSetsAt G v).card =
      2 ^ leafCount G v * (partialDomSets G v).card := by
  classical
  have hcard : ((leafNeighbors G v).powerset ×ˢ partialDomSets G v).card =
      (domSetsAt G v).card := by
    refine Finset.card_bij' (fun p _ => joinStem v p)
      (fun S _ => (S ∩ leafNeighbors G v, S ∩ remaining G v)) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hK, hT⟩ := mem_product.mp hp
      exact mem_domSetsAt.mpr ⟨dominating_stem_union hT (mem_powerset.mp hK),
        mem_insert_self _ _⟩
    · intro S hS
      obtain ⟨hd, hv⟩ := mem_domSetsAt.mp hS
      exact mem_product.mpr ⟨mem_powerset.mpr inter_subset_right,
        dominating_residual_partial hd hv⟩
    · intro p hp
      obtain ⟨hK, hT⟩ := mem_product.mp hp
      obtain ⟨h₁,h₂⟩ := split_intersections v p.1 p.2
        (mem_powerset.mp hK) (mem_partialDomSets.mp hT).1
      exact Prod.ext h₁ h₂
    · intro S hS
      exact split_reconstruct v S (mem_domSetsAt.mp hS).2
  rw [card_product, card_powerset] at hcard
  exact hcard.symm

/-- Twice the total cardinality over a powerset is its order times its size. -/
theorem powerset_card_sum (L : Finset V) :
    2 * (∑ K ∈ L.powerset, (K.card : ℚ)) = L.card * (2 : ℚ) ^ L.card := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | @insert x L hx ih =>
    rw [sum_powerset_insert hx]
    have hcard : ∀ K ∈ L.powerset, (insert x K).card = K.card + 1 := by
      intro K hK
      exact card_insert_of_notMem (fun h => hx (mem_powerset.mp hK h))
    have hins : (∑ K ∈ L.powerset, ((insert x K).card : ℚ)) =
        ∑ K ∈ L.powerset, ((K.card : ℚ) + 1) := by
      apply sum_congr rfl
      intro K hK
      rw [hcard K hK, Nat.cast_add, Nat.cast_one]
    rw [hins]
    rw [sum_add_distrib]
    simp only [sum_const, nsmul_eq_mul, mul_one, card_powerset, Nat.cast_pow,
      Nat.cast_ofNat, card_insert_of_notMem hx, Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

theorem stem_family_sum (G : SimpleGraph V) (v : V) (f : Finset V → ℚ) :
    (∑ p ∈ (leafNeighbors G v).powerset ×ˢ partialDomSets G v, f (joinStem v p)) =
      ∑ S ∈ domSetsAt G v, f S := by
  classical
  refine Finset.sum_bij' (fun p _ => joinStem v p)
    (fun S _ => (S ∩ leafNeighbors G v, S ∩ remaining G v)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hK, hT⟩ := mem_product.mp hp
    exact mem_domSetsAt.mpr ⟨dominating_stem_union hT (mem_powerset.mp hK),
      mem_insert_self _ _⟩
  · intro S hS
    obtain ⟨hd, hv⟩ := mem_domSetsAt.mp hS
    exact mem_product.mpr ⟨mem_powerset.mpr inter_subset_right,
      dominating_residual_partial hd hv⟩
  · intro p hp
    obtain ⟨hK, hT⟩ := mem_product.mp hp
    obtain ⟨h₁,h₂⟩ := split_intersections v p.1 p.2
      (mem_powerset.mp hK) (mem_partialDomSets.mp hT).1
    exact Prod.ext h₁ h₂
  · intro S hS
    exact split_reconstruct v S (mem_domSetsAt.mp hS).2
  · intro _ _
    rfl

theorem stem_card_sum (G : SimpleGraph V) (v : V) :
    2 * (∑ S ∈ domSetsAt G v, (S.card : ℚ)) =
      (2 : ℚ) ^ leafCount G v *
        ((2 + (leafCount G v : ℚ)) * (partialDomSets G v).card +
          2 * ∑ T ∈ partialDomSets G v, (T.card : ℚ)) := by
  classical
  rw [← stem_family_sum G v (fun S => (S.card : ℚ))]
  have hcard :
      (∑ p ∈ (leafNeighbors G v).powerset ×ˢ partialDomSets G v,
        ((joinStem v p).card : ℚ)) =
      ∑ p ∈ (leafNeighbors G v).powerset ×ˢ partialDomSets G v,
        (1 + (p.1.card : ℚ) + p.2.card) := by
    apply sum_congr rfl
    intro p hp
    obtain ⟨hK,hT⟩ := mem_product.mp hp
    rw [joinStem_card v p.1 p.2 (mem_powerset.mp hK) (mem_partialDomSets.mp hT).1]
    push_cast
    rfl
  rw [hcard, sum_product]
  simp_rw [sum_add_distrib]
  simp only [sum_const, nsmul_eq_mul, mul_one, card_powerset, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [← mul_sum]
  have hp := powerset_card_sum (leafNeighbors G v)
  unfold leafCount
  nlinarith

/-- The exact local mean consists of the stem, half its leaves, and the residual mean. -/
theorem avdAt_stem_split (G : SimpleGraph V) (v : V) :
    avdAt G v = 1 + (leafCount G v : ℚ) / 2 + familyAverage (partialDomSets G v) := by
  classical
  have ha : (partialDomSets G v).card ≠ 0 :=
    ne_of_gt (card_pos.mpr (partialDomSets_nonempty G v))
  have haq : ((partialDomSets G v).card : ℚ) ≠ 0 := by exact_mod_cast ha
  have hp : (2 : ℚ) ^ leafCount G v ≠ 0 := by positivity
  have hsum := stem_card_sum G v
  unfold avdAt familyAverage
  rw [stem_family_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  nlinarith [hsum]

end D5.S3.Combinatorics.Graph.LocalDominatingStemBoundSplit
