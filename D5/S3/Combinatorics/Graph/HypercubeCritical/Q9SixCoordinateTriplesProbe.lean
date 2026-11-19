module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Basic

/-! Triple families on six coordinates whose four-sets contain zero or two
selected triples. The parity rule recovers the family from the link of zero. -/

set_option autoImplicit false

open Finset

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

private abbrev Coordinates := Finset (Fin 6)
private abbrev Family := Finset Coordinates

private def pairs : Family := (univ : Coordinates).powersetCard 2
private def triples : Family := (univ : Coordinates).powersetCard 3
private def fours : Family := (univ : Coordinates).powersetCard 4
private def linkPairs : Family := ((univ : Coordinates).erase 0).powersetCard 2

private def fromLink (L : Family) : Family :=
  triples.filter fun t =>
    if 0 ∈ t then t.erase 0 ∈ L else (L.filter (· ⊆ t)).card % 2 = 1

private def shadow (T : Family) : Family :=
  pairs.filter fun p => (T.filter (p ⊆ ·)).Nonempty

private def valid (T : Family) : Prop :=
  (∀ s ∈ fours, (T.filter (· ⊆ s)).card ≤ 2) ∧
    ∀ p ∈ pairs, (T.filter (p ⊆ ·)).card ≤ 3

private def shape (T : Family) : ℕ × ℕ := (T.card, (shadow T).card)

private def outcomes : List (ℕ × ℕ) := [(0, 0), (6, 11), (8, 12), (8, 14), (10, 15)]

private def checkShape (T : Family) : Prop :=
  shape T ∈ outcomes ∧
    (shape T = (8, 12) → ∀ p ∈ pairs, (T.filter (Disjoint p ·)).card ≤ 2)

private instance (T : Family) : Decidable (valid T) := by unfold valid; infer_instance
private instance (T : Family) : Decidable (checkShape T) := by unfold checkShape; infer_instance

-- There are ten possible link edges, giving 1024 subsets of the fixed link.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 30000000 in
private theorem checked_links :
    ∀ L ∈ linkPairs.powerset, valid (fromLink L) → checkShape (fromLink L) := by
  decide +kernel

private def link (T : Family) : Family :=
  linkPairs.filter fun p => insert 0 p ∈ T

private lemma lift_link (T : Family) (h3 : ∀ t ∈ T, t.card = 3)
    (heven : ∀ s : Coordinates, s.card = 4 → Even (T.filter (· ⊆ s)).card) :
    fromLink (link T) = T := by
  ext t
  by_cases ht3 : t.card = 3
  · have hmem : t ∈ triples := by simp [triples, ht3]
    rw [fromLink, mem_filter, and_iff_right hmem]
    by_cases hzero : 0 ∈ t
    · rw [ite_eq_left hzero, link, mem_filter, insert_erase hzero]
      have ht : t.erase 0 ∈ linkPairs := by
        simp [linkPairs, mem_powersetCard, erase_subset_erase, card_erase_of_mem hzero, ht3]
      simp [ht]
    · rw [ite_eq_right hzero]
      let s := insert 0 t
      let A := (T.filter (· ⊆ s)).filter fun u => 0 ∈ u
      let B := (T.filter (· ⊆ s)).filter fun u => 0 ∉ u
      have hA : ( (link T).filter (· ⊆ t)).card = A.card := by
        apply card_bij (fun p _ => insert 0 p)
        · intro p hp
          obtain ⟨hpL, hpt⟩ := mem_filter.mp hp
          have hpT := (mem_filter.mp hpL).2
          exact mem_filter.mpr
            ⟨mem_filter.mpr ⟨hpT, insert_subset_insert _ hpt⟩, mem_insert_self _ _⟩
        · intro p hp q hq h
          exact (erase_insert (fun hz => hzero ((mem_filter.mp hp).2 hz))).symm.trans
            ((congrArg (fun u : Coordinates => u.erase 0) h).trans
              (erase_insert (fun hz => hzero ((mem_filter.mp hq).2 hz))))
        · intro u hu
          obtain ⟨huS, hzu⟩ := mem_filter.mp hu
          obtain ⟨huT, hus⟩ := mem_filter.mp huS
          have hut : u.erase 0 ⊆ t := by
            intro i hi
            rcases mem_insert.mp (hus (mem_erase.mp hi).2) with e | hit
            · exact False.elim ((mem_erase.mp hi).1 e)
            · exact hit
          have he := insert_erase hzu
          have hp : u.erase 0 ∈ linkPairs := by
            rw [linkPairs, mem_powersetCard, card_erase_of_mem hzu, h3 u huT]
            exact ⟨fun i hi => mem_erase.mpr ⟨(mem_erase.mp hi).1, mem_univ _⟩, rfl⟩
          exact ⟨u.erase 0, mem_filter.mpr ⟨mem_filter.mpr ⟨hp, he.symm ▸ huT⟩, hut⟩, he⟩
      have hB : B.card = if t ∈ T then 1 else 0 := by
        have hEq : B = if t ∈ T then {t} else ∅ := by
          ext u
          constructor
          · intro hu
            obtain ⟨huS, hzu⟩ := mem_filter.mp hu
            obtain ⟨huT, hus⟩ := mem_filter.mp huS
            have hut : u ⊆ t := fun i hi => (mem_insert.mp (hus hi)).resolve_left
              (fun e => hzu (e ▸ hi))
            have he := eq_of_subset_of_card_le hut (by rw [h3 u huT, ht3])
            subst u
            simp [huT]
          · intro hu
            by_cases h : t ∈ T
            · rw [ite_eq_left h, mem_singleton] at hu
              subst u
              exact mem_filter.mpr ⟨mem_filter.mpr ⟨h, subset_insert _ _⟩, hzero⟩
            · simp [h] at hu
        rw [hEq]
        split_ifs <;> simp
      have ht4 : s.card = 4 := by rw [show s = insert 0 t from rfl,
        card_insert_of_notMem hzero, ht3]
      have hpart := card_filter_add_card_filter_not (s := T.filter (· ⊆ s))
        (fun u => 0 ∈ u)
      change A.card + B.card = _ at hpart
      obtain ⟨n, hn⟩ := heven s ht4
      rw [← hpart, ← hA, hB] at hn
      by_cases h : t ∈ T <;> simp [h] at hn ⊢ <;> omega
  · have hn : t ∉ T := fun h => ht3 (h3 t h)
    simp [fromLink, triples, ht3, hn]

/-- The possible triple and pair-shadow counts under four-set parity and the
local incidence bounds. A family of shape `(8, 12)` has at most two triples
disjoint from any given pair. -/
public theorem six_coordinate_triple_family_shapes (T : Finset (Finset (Fin 6)))
    (h3 : ∀ t ∈ T, t.card = 3)
    (h4 : ∀ s : Finset (Fin 6), s.card = 4 →
      Even (T.filter (· ⊆ s)).card ∧ (T.filter (· ⊆ s)).card ≤ 2)
    (h2 : ∀ p : Finset (Fin 6), p.card = 2 → (T.filter (p ⊆ ·)).card ≤ 3) :
    let P := ((univ : Finset (Fin 6)).powersetCard 2).filter
      fun p => (T.filter (p ⊆ ·)).Nonempty
    (T.card, P.card) ∈ ([(0, 0), (6, 11), (8, 12), (8, 14), (10, 15)] : List (ℕ × ℕ)) ∧
      (T.card = 8 → P.card = 12 → ∀ p : Finset (Fin 6), p.card = 2 →
        (T.filter (Disjoint p ·)).card ≤ 2) := by
  change shape T ∈ outcomes ∧
    (T.card = 8 → (shadow T).card = 12 → ∀ p : Coordinates, p.card = 2 →
      (T.filter (Disjoint p ·)).card ≤ 2)
  have hvalid : valid T := by
    constructor
    · intro s hs
      exact (h4 s (mem_powersetCard.mp hs).2).2
    · intro p hp
      exact h2 p (mem_powersetCard.mp hp).2
  have he := lift_link T h3 (fun s hs => (h4 s hs).1)
  have hcalc := checked_links (link T) (mem_powerset.mpr (filter_subset _ _))
    (by rw [he]; exact hvalid)
  rw [he] at hcalc
  exact ⟨hcalc.1, fun ht hp p hcard =>
    hcalc.2 (Prod.ext ht hp) p (by simp [pairs, hcard])⟩

#print axioms six_coordinate_triple_family_shapes

end D5.S3.Combinatorics.Graph.HypercubeCritical
