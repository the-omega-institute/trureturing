/- GID: D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping.result; premises=D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.four_pair_data,D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.baseTwoPairing,D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.baseThreePairing
   digest: Brauer complete-mapping existence constructions and classification. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSubsetPairing.rank_two_subset_pairing
proof_shape: content — iterate_subset_pairing, rank_two_subset_pairing, rank_three_subset_pairing
proof_shape: bind-only — pairLookup, fourPairs, fourPair, four_pair_data, SubsetPairing, extendPair, extend_pair_card, extend_pair_involutive, inter_disjSum, extend_pair_fixed, extend_pair_adjacent, SubsetPairing.extend, SubsetPairing.map, baseTwoPairs, baseTwoTriangle, baseTwoPairing, baseThreePairs, baseThreeTriangle, baseThreePairing, SubsetPairing.pair, SubsetPairing.involutive, SubsetPairing.card, SubsetPairing.fixed, SubsetPairing.adjacent
Direct frozen dependencies (declaration statement_id):
none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24053
-/

import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.GroupTheory.Perm.Basic
import Lean.Elab.Tactic.LibrarySearch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Order.Setoid.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Lucas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSubsetPairing

open Equiv
open scoped BigOperators

open Finset

private def pairLookup {X : Type*} [DecidableEq X] (pairs : List (X × X)) (x : X) : X :=
  match pairs with
  | [] => x
  | (a,b) :: rest => if x = a then b else if x = b then a else pairLookup rest x

private def fourPairs : List (Finset (Fin 4) × Finset (Fin 4)) :=
  [({0},{1}), ({2},{3}),
   ({0,1},{0,2}), ({0,3},{1,3}), ({1,2},{2,3}),
   ({0,1,2},{0,1,3}), ({0,2,3},{1,2,3})]

private def fourPair : Finset (Fin 4) → Finset (Fin 4) := pairLookup fourPairs

private theorem four_pair_data :
    Function.Involutive fourPair ∧
    (∀ s, (fourPair s).card = s.card) ∧
    (∀ s : Finset (Fin 4), s.Nonempty → s.card ≤ 3 →
      fourPair s ≠ s ∧ (s ∩ fourPair s).card + 1 = s.card) := by
  unfold Function.Involutive
  decide

structure SubsetPairing (X : Type*) [DecidableEq X] (r : ℕ)
    (triangle : Finset (Finset X)) where
  pair : Finset X → Finset X
  involutive : Function.Involutive pair
  card : ∀ s, (pair s).card = s.card
  fixed : ∀ s, s.card = r → (pair s = s ↔ s ∈ triangle)
  adjacent : ∀ s, s.card = r → s ∉ triangle → (s ∩ pair s).card + 1 = r

private def extendPair {X : Type*} [DecidableEq X] (f : Finset X → Finset X)
    (s : Finset (X ⊕ Fin 4)) : Finset (X ⊕ Fin 4) :=
  if s.toRight = ∅ then (f s.toLeft).disjSum ∅
  else s.toLeft.disjSum (fourPair s.toRight)

private theorem extend_pair_card {X : Type*} [DecidableEq X]
    (f : Finset X → Finset X) (hf : ∀ s, (f s).card = s.card)
    (s : Finset (X ⊕ Fin 4)) : (extendPair f s).card = s.card := by
  unfold extendPair
  split_ifs with h
  · simpa only [card_disjSum, hf, card_empty, add_zero, h] using
      s.card_toLeft_add_card_toRight
  · rw [card_disjSum, four_pair_data.2.1]
    exact s.card_toLeft_add_card_toRight

private theorem extend_pair_involutive {X : Type*} [DecidableEq X]
    (f : Finset X → Finset X) (hf : Function.Involutive f) :
    Function.Involutive (extendPair f) := by
  intro s
  by_cases hs : s.toRight = ∅
  · simp only [extendPair, hs, ite_true, ite_false, toRight_disjSum, toLeft_disjSum, hf s.toLeft]
    simpa only [hs] using s.toLeft_disjSum_toRight
  · have hne : fourPair s.toRight ≠ ∅ := by
      intro h
      have hc := four_pair_data.2.1 s.toRight
      rw [h, card_empty] at hc
      exact hs (card_eq_zero.mp hc.symm)
    simp only [extendPair, hs, ite_true, ite_false, toRight_disjSum, toLeft_disjSum,
      hne, four_pair_data.1 s.toRight]
    exact s.toLeft_disjSum_toRight

private theorem inter_disjSum {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (a c : Finset X) (b d : Finset Y) :
    a.disjSum b ∩ c.disjSum d = (a ∩ c).disjSum (b ∩ d) :=
  (Finset.sumEquiv.symm.map_inf (a,b) (c,d)).symm

private theorem extend_pair_fixed {X : Type*} [DecidableEq X]
    {r : ℕ} {tri : Finset (Finset X)} (h : SubsetPairing X r tri)
    (hr : r ≤ 3) (s : Finset (X ⊕ Fin 4)) (hs : s.card = r) :
    extendPair h.pair s = s ↔
      s ∈ tri.image (fun t => t.disjSum (∅ : Finset (Fin 4))) := by
  by_cases he : s.toRight = ∅
  · have hc : s.toLeft.card = r := by
      have := s.card_toLeft_add_card_toRight
      rw [he, card_empty, add_zero, hs] at this
      exact this
    rw [extendPair, ite_eq_left he]
    have hse : s.toLeft.disjSum (∅ : Finset (Fin 4)) = s := by
      simpa only [he] using s.toLeft_disjSum_toRight
    constructor
    · intro hf
      have hleft := congrArg Finset.toLeft hf
      simp only [toLeft_disjSum] at hleft
      exact mem_image.mpr ⟨s.toLeft, (h.fixed _ hc).mp hleft, hse⟩
    · intro ht
      obtain ⟨t, ht, hts⟩ := mem_image.mp ht
      have heq := congrArg Finset.toLeft hts
      simp only [toLeft_disjSum] at heq
      rw [(h.fixed _ hc).mpr (heq ▸ ht)]
      exact hse
  · have hcard : s.toRight.card ≤ 3 := by
      have := s.card_toRight_le
      omega
    have hfree := (four_pair_data.2.2 s.toRight (nonempty_iff_ne_empty.mpr he) hcard).1
    constructor
    · intro hf
      have hc := congrArg Finset.toRight hf
      simp only [extendPair, he, ite_false, toRight_disjSum] at hc
      exact (hfree hc).elim
    · intro ht
      obtain ⟨t, _, hts⟩ := mem_image.mp ht
      have hz := congrArg Finset.toRight hts
      simp only [toRight_disjSum] at hz
      exact (he hz.symm).elim

private theorem extend_pair_adjacent {X : Type*} [DecidableEq X]
    {r : ℕ} {tri : Finset (Finset X)} (h : SubsetPairing X r tri)
    (hr : r ≤ 3) (s : Finset (X ⊕ Fin 4)) (hs : s.card = r)
    (ht : s ∉ tri.image (fun t => t.disjSum (∅ : Finset (Fin 4)))) :
    (s ∩ extendPair h.pair s).card + 1 = r := by
  by_cases he : s.toRight = ∅
  · have hc : s.toLeft.card = r := by
      have := s.card_toLeft_add_card_toRight
      rw [he, card_empty, add_zero, hs] at this
      exact this
    have htri : s.toLeft ∉ tri := by
      intro hmem
      apply ht
      exact mem_image.mpr ⟨s.toLeft, hmem, by simpa only [he] using s.toLeft_disjSum_toRight⟩
    have hadj := h.adjacent _ hc htri
    rw [extendPair, ite_eq_left he, ← s.toLeft_disjSum_toRight, he, inter_disjSum]
    simpa only [toLeft_disjSum, inter_empty, card_disjSum, card_empty, add_zero] using hadj
  · have hcard : s.toRight.card ≤ 3 := by
      have := s.card_toRight_le
      omega
    have hadj := (four_pair_data.2.2 s.toRight (nonempty_iff_ne_empty.mpr he) hcard).2
    rw [extendPair, ite_eq_right he, ← s.toLeft_disjSum_toRight, inter_disjSum,
      toLeft_disjSum, toRight_disjSum, card_disjSum, inter_self]
    have hc := s.card_toLeft_add_card_toRight
    omega

private def SubsetPairing.extend {X : Type*} [DecidableEq X] {r : ℕ}
    {tri : Finset (Finset X)} (h : SubsetPairing X r tri) (hr : r ≤ 3) :
    SubsetPairing (X ⊕ Fin 4) r
      (tri.image (fun t => t.disjSum (∅ : Finset (Fin 4)))) where
  pair := extendPair h.pair
  involutive := extend_pair_involutive h.pair h.involutive
  card := extend_pair_card h.pair h.card
  fixed := extend_pair_fixed h hr
  adjacent := extend_pair_adjacent h hr

private noncomputable def SubsetPairing.map {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {r : ℕ} {tri : Finset (Finset X)} (h : SubsetPairing X r tri) (e : X ≃ Y) :
    SubsetPairing Y r (tri.image (Equiv.finsetCongr e)) where
  pair s := (Equiv.finsetCongr e) (h.pair ((Equiv.finsetCongr e).symm s))
  involutive := by
    intro s
    dsimp only
    rw [(Equiv.finsetCongr e).symm_apply_apply, h.involutive,
      (Equiv.finsetCongr e).apply_symm_apply]
  card := by
    intro s
    simp only [Equiv.finsetCongr_apply, Equiv.finsetCongr_symm, card_map, h.card]
  fixed := by
    intro s hs
    let ef := Equiv.finsetCongr e
    have hc : (ef.symm s).card = r := by
      simpa only [ef, Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, card_map] using hs
    constructor
    · intro he
      have hf : h.pair (ef.symm s) = ef.symm s := by
        apply ef.injective
        exact he.trans (ef.apply_symm_apply s).symm
      exact mem_image.mpr ⟨ef.symm s, (h.fixed _ hc).mp hf, ef.apply_symm_apply s⟩
    · intro ht
      obtain ⟨t, ht, hts⟩ := mem_image.mp ht
      have he : ef.symm s = t := by exact (Equiv.symm_apply_eq ef).mpr (id (Eq.symm hts))
      change ef (h.pair (ef.symm s)) = s
      rw [he, (h.fixed t (he ▸ hc)).mpr ht]
      exact hts
  adjacent := by
    intro s hs ht
    let ef := Equiv.finsetCongr e
    have hc : (ef.symm s).card = r := by
      simpa only [ef, Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, card_map] using hs
    have hnt : ef.symm s ∉ tri := by
      intro hm
      exact ht (mem_image.mpr ⟨ef.symm s, hm, ef.apply_symm_apply s⟩)
    have hadj := h.adjacent (ef.symm s) hc hnt
    have hi : s ∩ ef (h.pair (ef.symm s)) = ef (ef.symm s ∩ h.pair (ef.symm s)) := by
      change s ∩ (h.pair (ef.symm s)).map e.toEmbedding =
        (ef.symm s ∩ h.pair (ef.symm s)).map e.toEmbedding
      rw [Finset.map_inter]
      change s ∩ (h.pair (ef.symm s)).map e.toEmbedding =
        ef (ef.symm s) ∩ (h.pair (ef.symm s)).map e.toEmbedding
      rw [ef.apply_symm_apply]
    change (s ∩ ef (h.pair (ef.symm s))).card + 1 = r
    rw [hi]
    simpa only [ef, Equiv.finsetCongr_apply, card_map] using hadj

private def baseTwoPairs : List (Finset (Fin 6) × Finset (Fin 6)) :=
  [({1,3},{0,3}),
   ({2,3},{2,4}),
   ({0,4},{0,5}),
   ({3,4},{1,4}),
   ({3,5},{1,5}),
   ({4,5},{2,5})]

def baseTwoTriangle : Finset (Finset (Fin 6)) :=
  {{0,1},{0,2},{1,2}}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private def baseTwoPairing : SubsetPairing (Fin 6) 2 baseTwoTriangle where
  pair := pairLookup baseTwoPairs
  involutive := by unfold Function.Involutive; decide
  card := by decide
  fixed := by decide
  adjacent := by decide

private def baseThreePairs : List (Finset (Fin 7) × Finset (Fin 7)) :=
  [({0,1,2},{0,1,4}),
   ({0,3,4},{0,2,4}),
   ({1,2,4},{1,2,5}),
   ({1,3,4},{1,3,5}),
   ({2,3,4},{2,3,5}),
   ({2,4,5},{0,2,5}),
   ({3,4,5},{0,3,5}),
   ({0,1,5},{0,1,6}),
   ({0,4,5},{0,4,6}),
   ({1,4,5},{1,4,6}),
   ({1,5,6},{0,5,6}),
   ({4,5,6},{2,4,6}),
   ({2,5,6},{0,2,6}),
   ({1,2,6},{1,3,6}),
   ({3,4,6},{0,3,6}),
   ({3,5,6},{2,3,6})]

def baseThreeTriangle : Finset (Finset (Fin 7)) :=
  {{0,1,3},{0,2,3},{1,2,3}}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private def baseThreePairing : SubsetPairing (Fin 7) 3 baseThreeTriangle where
  pair := pairLookup baseThreePairs
  involutive := by unfold Function.Involutive; decide
  card := by decide
  fixed := by decide
  adjacent := by decide

private theorem iterate_subset_pairing {n r : ℕ} {tri : Finset (Finset (Fin n))}
    (h : SubsetPairing (Fin n) r tri) (hr : r ≤ 3) (k : ℕ) :
    ∃ e : Fin n ↪ Fin (n + 4 * k),
      Nonempty (SubsetPairing (Fin (n + 4 * k)) r
        (tri.image (fun s => s.map e))) := by
  induction k with
  | zero =>
    refine ⟨Function.Embedding.refl _, ?_⟩
    simpa using (show Nonempty (SubsetPairing (Fin n) r tri) from ⟨h⟩)
  | succ k ih =>
    obtain ⟨e, ⟨H⟩⟩ := ih
    let E : (Fin (n + 4 * k) ⊕ Fin 4) ≃ Fin (n + 4 * (k + 1)) :=
      finSumFinEquiv.trans (finCongr (by omega))
    let j : Fin n ↪ Fin (n + 4 * (k + 1)) :=
      (e.trans Function.Embedding.inl).trans E.toEmbedding
    refine ⟨j, ?_⟩
    have HH := (H.extend hr).map E
    have heq :
        (((tri.image (fun s => s.map e)).image
          (fun t => t.disjSum (∅ : Finset (Fin 4)))).image
          (Equiv.finsetCongr E)) = tri.image (fun s => s.map j) := by
      rw [image_image, image_image]
      congr 1
      funext s
      simp only [Function.comp_apply, Equiv.finsetCongr_apply, disjSum_empty, map_map]
      rfl
    rw [heq] at HH
    exact ⟨HH⟩

theorem rank_two_subset_pairing (k : ℕ) :
    ∃ e : Fin 6 ↪ Fin (6 + 4 * k),
      Nonempty (SubsetPairing (Fin (6 + 4 * k)) 2
        (baseTwoTriangle.image (fun s => s.map e))) := by
  exact iterate_subset_pairing baseTwoPairing (by decide) k

theorem rank_three_subset_pairing (k : ℕ) :
    ∃ e : Fin 7 ↪ Fin (7 + 4 * k),
      Nonempty (SubsetPairing (Fin (7 + 4 * k)) 3
        (baseThreeTriangle.image (fun s => s.map e))) := by
  exact iterate_subset_pairing baseThreePairing (by decide) k

end D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSubsetPairing
