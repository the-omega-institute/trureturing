/- GID: D5/S3/Combinatorics/Graph/Brooks/Subcubic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Brooks/Subcubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic.Push]
   utility: none
   digest: Finite subcubic four-clique-free graphs admit three colors. -/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.Push
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic.NormNum
import D5.S3.Combinatorics.Graph.Brooks.Coloring
import D5.S3.Combinatorics.Graph.Brooks.Cuts
import D5.S3.Combinatorics.Graph.Brooks.Endblock

/-!
This source transplant is from Juan Pablo Traverso Gianini's BrooksSubcubic proof:
https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic
Author source: https://github.com/jtraverso/lean-pool/tree/aced439fd4161d118bf167a1e8d10553f28913fe
The complete Apache-2.0 license and NOTICE chain are retained in
`docs/reports/brooks-suppliers/lean-pool-LICENSE.txt` and `lean-pool-NOTICE.txt`.
Packaging is adapted to repository imports; `dif_pos` and `dif_neg` implement
this repository's pinned API for dependent-if reduction.
Retire these transplants when this repository's pinned Mathlib provides equivalent
statements, and replace all consumers by direct applications of those declarations.
-/

/- Source unit: LeanPool/BrooksSubcubic/K4Free.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Subcubic Brooks theorem: K4Free

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

/-- In a K₄-free graph, a degree-3 vertex has two non-adjacent neighbours. -/
theorem exists_nonadj_pair_of_cubic_K4free (G : SimpleGraph V) [DecidableRel G.Adj]
    (hK4 : G.CliqueFree 4) {v₀ : V} (hdeg : G.degree v₀ = 3) :
    ∃ a b, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b := by
  classical
  have hcard : (G.neighborFinset v₀).card = 3 := by rw [G.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hcard
  have hmem : ∀ w ∈ G.neighborFinset v₀, G.Adj v₀ w := fun w hw => by
    rw [mem_neighborFinset] at hw
    exact hw
  have ha : G.Adj v₀ a := hmem a (by rw [hset]; exact Finset.mem_insert_self _ _)
  have hb : G.Adj v₀ b := hmem b (by rw [hset]; simp)
  have hc : G.Adj v₀ c := hmem c (by rw [hset]; simp)
  by_contra hcon
  push Not at hcon
  have hnab : G.Adj a b := hcon a b ha hb hab
  have hnac : G.Adj a c := hcon a c ha hc hac
  have hnbc : G.Adj b c := hcon b c hb hc hbc
  have hv0a : v₀ ≠ a := ha.ne
  have hv0b : v₀ ≠ b := hb.ne
  have hv0c : v₀ ≠ c := hc.ne
  refine hK4 {v₀, a, b, c} ?_
  refine ⟨?_, ?_⟩
  · intro y hy z hz hyz
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hy hz
    rcases hy with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hyz
        | assumption
        | (exact ha) | (exact hb) | (exact hc)
        | (exact hnab) | (exact hnac) | (exact hnbc)
        | (exact ha.symm) | (exact hb.symm) | (exact hc.symm)
        | (exact hnab.symm) | (exact hnac.symm) | (exact hnbc.symm)
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hbc]
    · simp [hac, hab]
    · simp [hv0a, hv0b, hv0c]

end BrooksSubcubic
end

/- Source unit: LeanPool/BrooksSubcubic/NoCutTriple.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# A good triple in a cubic graph without cut vertices

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section
open SimpleGraph Finset

namespace BrooksSubcubic

theorem cubic_good_triple_of_no_cut {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : ∀ v : V, G.degree v = 3)
    (hK4 : G.CliqueFree 4)
    (hnocut : ∀ x : V, (G.induce ({x}ᶜ : Set V)).Connected) :
    ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b ∧
      (G.induce (({a, b} : Set V)ᶜ)).Connected := by
  classical
  obtain ⟨v⟩ := hconn.nonempty
  obtain ⟨a₀, b₀, hva, hvb, hab, hnab⟩ :=
    BrooksSubcubic.exists_nonadj_pair_of_cubic_K4free G hK4 (hreg v)
  obtain ⟨u, b, hua, hub, hnab', hba⟩ :=
    BrooksSubcubic.exists_dist2_pair G hconn hab.symm hnab
  by_cases hall : ∀ y, y ≠ a₀ → (G.induce (({a₀, y} : Set V)ᶜ)).Connected
  · exact ⟨u, a₀, b, hua.symm, hub, hba.symm, hnab', hall b hba⟩
  · push Not at hall
    obtain ⟨y, hay, hcut⟩ := hall
    by_cases hb0y : b₀ = y
    · have hvay : v ∉ ({a₀, y} : Set V) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hva.ne, fun hvy => hvb.ne (hvy.trans hb0y.symm)⟩
      exact BrooksSubcubic.good_triple_of_two_cut G hreg hnocut a₀ y v hay.symm hvay hcut
    · have hb0ay : b₀ ∉ ({a₀, y} : Set V) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hab.symm, hb0y⟩
      exact BrooksSubcubic.good_triple_of_two_cut G hreg hnocut a₀ y b₀ hay.symm hb0ay hcut
end BrooksSubcubic
end

/- Source unit: LeanPool/BrooksSubcubic/GoodTriple.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Subcubic Brooks theorem: GoodTriple

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section
open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

/-- Contrapositive form of the Lovász lemma specialized to cubic K₄-free graphs. -/
theorem good_triple_of_all_vertex_deletions_connected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : ∀ v, G.degree v = 3) (hK4 : G.CliqueFree 4)
    (hdel : ∀ x, (G.induce ({x}ᶜ : Set V)).Connected) :
    ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b ∧
      (G.induce (({a, b} : Set V)ᶜ)).Connected :=
  cubic_good_triple_of_no_cut G hconn hreg hK4 hdel

/-- **Lovász cut-existence step.** A connected cubic K₄-free graph with no good triple
has a cut vertex, presented directly by two unreachable vertices after deletion. -/
theorem cut_witness_of_no_good_triple
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : ∀ v, G.degree v = 3) (hK4 : G.CliqueFree 4)
    (hng : ¬ ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b ∧
      (G.induce (({a, b} : Set V)ᶜ)).Connected) :
    ∃ (x d e : V) (hd : d ≠ x) (he : e ≠ x),
      ¬ (G.induce ({x}ᶜ : Set V)).Reachable ⟨d, hd⟩ ⟨e, he⟩ := by
  classical
  have hcut : ∃ x, ¬ (G.induce ({x}ᶜ : Set V)).Connected := by
    by_contra h
    push Not at h
    exact hng (good_triple_of_all_vertex_deletions_connected G hconn hreg hK4 h)
  obtain ⟨x, hx⟩ := hcut
  obtain ⟨a, b, hxa, hxb, hab, hnab⟩ :=
    exists_nonadj_pair_of_cubic_K4free G hK4 (hreg x)
  obtain ⟨d, e, hd, he, hde⟩ := exists_unreachable_of_cutVertex G x a hxa.ne' hx
  exact ⟨x, d, e, hd, he, hde⟩

end BrooksSubcubic
end

/- Source unit: LeanPool/BrooksSubcubic/CutColouring.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Subcubic Brooks theorem: CutColouring

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Induced degree never exceeds the ambient degree. -/
theorem induce_degree_le (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    [DecidablePred (· ∈ S)] [DecidableRel (G.induce S).Adj] (w : ↥S) :
    (G.induce S).degree w ≤ G.degree w.val := by
  classical
  have hsub : ((G.induce S).neighborFinset w).image Subtype.val ⊆ G.neighborFinset w.val := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [mem_neighborFinset] at hy ⊢
    simpa [SimpleGraph.induce, SimpleGraph.comap] using hy
  calc (G.induce S).degree w
      = ((G.induce S).neighborFinset w).card := ((G.induce S).card_neighborFinset_eq_degree w).symm
    _ = (((G.induce S).neighborFinset w).image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.neighborFinset w.val).card := Finset.card_le_card hsub
    _ = G.degree w.val := G.card_neighborFinset_eq_degree _

omit [DecidableEq V] in
/-- An outside neighbour supplies the low-degree vertex needed to colour a connected piece. -/
private theorem colorable_induce_of_outside_neighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) (hconn : (G.induce S).Connected)
    (hdeg : ∀ v, G.degree v ≤ 3) (x : ↥S) (z : V)
    (hz : z ∉ S) (hadj : G.Adj x.val z) : (G.induce S).Colorable 3 := by
  classical
  apply connected_colorable_three_of_exists_degree_lt _ hconn
  · intro v
    exact (induce_degree_le G S v).trans (hdeg v.val)
  · refine ⟨x, ?_⟩
    have hsub : ((G.induce S).neighborFinset x).image Subtype.val
        ⊆ (G.neighborFinset x.val).erase z := by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_erase, mem_neighborFinset]
      refine ⟨?_, ?_⟩
      · intro h
        exact hz (h ▸ w.property)
      · rw [mem_neighborFinset] at hw
        simpa [SimpleGraph.induce, SimpleGraph.comap] using hw
    have hzmem : z ∈ G.neighborFinset x.val := by rw [mem_neighborFinset]; exact hadj
    calc (G.induce S).degree x
        = ((G.induce S).neighborFinset x).card :=
          ((G.induce S).card_neighborFinset_eq_degree x).symm
      _ = (((G.induce S).neighborFinset x).image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ ((G.neighborFinset x.val).erase z).card := Finset.card_le_card hsub
      _ = G.degree x.val - 1 := by
          rw [Finset.card_erase_of_mem hzmem, G.card_neighborFinset_eq_degree]
      _ < 3 := by have := hdeg x.val; omega

/-- **B, cut-vertex reduction (structural half).** Given a 3-regular `G`, a vertex `x`, and a
partition of `V∖{x}` into nonempty `A₀,B₀` with no edge crossing between them, such that both
`G[{x}∪A₀]` and `G[{x}∪B₀]` are connected, `G` is 3-colourable: each side has `x` at degree `< 3`
(it has a neighbour on the other side), so the non-regular case colours it, and the glue lemma
merges them at `x`. This discharges everything downstream of the Lovász cut-existence step. -/
theorem colorable_of_cut_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3)
    (x : V) (A₀ B₀ : Finset V)
    (hAne : A₀.Nonempty) (hBne : B₀.Nonempty)
    (hxnA : x ∉ A₀) (hxnB : x ∉ B₀)
    (hdisj : Disjoint A₀ B₀)
    (hcov : insert x (A₀ ∪ B₀) = Finset.univ)
    (hnocross : ∀ a ∈ A₀, ∀ b ∈ B₀, ¬ G.Adj a b)
    (hAconn : (G.induce ((insert x A₀ : Finset V) : Set V)).Connected)
    (hBconn : (G.induce ((insert x B₀ : Finset V) : Set V)).Connected) :
    G.Colorable 3 := by
  classical
  set A : Finset V := insert x A₀ with hA
  set B : Finset V := insert x B₀ with hB
  have hxA : x ∈ A := Finset.mem_insert_self _ _
  have hxB : x ∈ B := Finset.mem_insert_self _ _
  have hcover : A ∪ B = Finset.univ := by
    rw [hA, hB, Finset.insert_union, Finset.union_insert, ← hcov]
    rw [Finset.insert_idem]
  have : DecidableRel (G.induce ((A : Finset V) : Set V)).Adj := Classical.decRel _
  have : DecidableRel (G.induce ((B : Finset V) : Set V)).Adj := Classical.decRel _
  have hxneighbor : ∀ (C₀ : Finset V), C₀.Nonempty → x ∉ C₀ →
      (G.induce ((insert x C₀ : Finset V) : Set V)).Connected →
      ∃ z ∈ C₀, G.Adj x z := by
    intro C₀ hCne hxnC hCconn
    obtain ⟨c₀, hc₀⟩ := hCne
    have hxmem : x ∈ ((insert x C₀ : Finset V) : Set V) := by
      simp
    have hcmem : c₀ ∈ ((insert x C₀ : Finset V) : Set V) := by
      simp [hc₀]
    have hne : (⟨x, hxmem⟩ : ↥((insert x C₀ : Finset V) : Set V)) ≠ ⟨c₀, hcmem⟩ := by
      intro h
      apply hxnC
      have : x = c₀ := congrArg Subtype.val h
      rw [this]; exact hc₀
    obtain ⟨p⟩ := hCconn.preconnected ⟨x, hxmem⟩ ⟨c₀, hcmem⟩
    cases p with
    | nil => exact absurd rfl hne
    | cons hadj q =>
        rename_i z
        refine ⟨z.val, ?_, ?_⟩
        · have hzmem := z.property
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hzmem
          have hzx : z.val ≠ x := by
            intro h
            have : G.Adj x x := by
              have : G.Adj x z.val := by simpa [SimpleGraph.induce, SimpleGraph.comap] using hadj
              rw [h] at this
              exact this
            exact this.ne rfl
          rcases hzmem with h | h
          · exact absurd h hzx
          · exact h
        · simpa [SimpleGraph.induce, SimpleGraph.comap] using hadj
  obtain ⟨bz, hbz0, hxbz⟩ := hxneighbor B₀ hBne hxnB hBconn
  obtain ⟨az, haz0, hxaz⟩ := hxneighbor A₀ hAne hxnA hAconn
  have hbznotA : bz ∉ A := by
    rw [hA, Finset.mem_insert]; push Not
    exact ⟨fun h => hxnB (h ▸ hbz0), fun h => (Finset.disjoint_left.mp hdisj h) hbz0⟩
  have haznotB : az ∉ B := by
    rw [hB, Finset.mem_insert]; push Not
    exact ⟨fun h => hxnA (h ▸ haz0), fun h => (Finset.disjoint_right.mp hdisj h) haz0⟩
  have hdeg : ∀ v, G.degree v ≤ 3 := fun v => le_of_eq (hreg v)
  have hApiece := colorable_induce_of_outside_neighbor G (A : Set V) hAconn
    hdeg ⟨x, hxA⟩ bz hbznotA hxbz
  have hBpiece := colorable_induce_of_outside_neighbor G (B : Set V) hBconn
    hdeg ⟨x, hxB⟩ az haznotB hxaz
  have hcross : ∀ u ∈ A, ∀ w ∈ B, u ≠ x → w ≠ x → ¬ G.Adj u w := by
    intro u hu w hw hux hwx
    have huA0 : u ∈ A₀ := by
      rw [hA, Finset.mem_insert] at hu; exact hu.resolve_left hux
    have hwB0 : w ∈ B₀ := by
      rw [hB, Finset.mem_insert] at hw; exact hw.resolve_left hwx
    exact hnocross u huA0 w hwB0
  exact colorable_glue_at_vertex G A B x hcover hxA hxB hcross hApiece hBpiece

end BrooksSubcubic
end

/- Source unit: LeanPool/BrooksSubcubic/CubicColouring.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/



/-!
# Subcubic Brooks theorem: CubicColouring

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` with all edges incident to `v₀` removed (same vertex set). -/
def deleteStar (G : SimpleGraph V) (v₀ : V) : SimpleGraph V :=
  G.deleteIncidenceSet v₀

omit [Fintype V] [DecidableEq V] in
/-- Adjacency in the graph with the edges at v₀ removed. -/
theorem deleteStar_adj (G : SimpleGraph V) (v₀ x y : V) :
    (deleteStar G v₀).Adj x y ↔ G.Adj x y ∧ x ≠ v₀ ∧ y ≠ v₀ :=
  SimpleGraph.deleteIncidenceSet_adj

omit [Fintype V] in
instance (G : SimpleGraph V) [DecidableRel G.Adj] (v₀ : V) :
    DecidableRel (deleteStar G v₀).Adj := fun x y =>
  decidable_of_iff (G.Adj x y ∧ x ≠ v₀ ∧ y ≠ v₀) (deleteStar_adj G v₀ x y).symm

/-- Neighbours of `x ≠ v₀` in `deleteStar G v₀` are exactly `N_G(x)` with `v₀` erased. -/
theorem deleteStar_neighborFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v₀ x : V)
    (hx : x ≠ v₀) :
    (deleteStar G v₀).neighborFinset x = (G.neighborFinset x).erase v₀ := by
  classical
  ext w
  simp only [SimpleGraph.mem_neighborFinset, deleteStar_adj, Finset.mem_erase]
  constructor
  · rintro ⟨hadj, _, hw⟩; exact ⟨hw, hadj⟩
  · rintro ⟨hw, hadj⟩; exact ⟨hadj, hx, hw⟩

/-- **A2 (rank from a descent function).** Given `v₀` with non-adjacent neighbours `a,b`, a
3-regular `G`, and a level function `lvl` (think: BFS distance in `G−{a,b}` from `v₀`) with
`lvl x < |V|` and the descent property (every non-`v₀` non-neighbour of `v₀`, other than `a,b`,
has a `G`-neighbour `≠ v₀,a,b` of strictly smaller level), there is an injective `rank` giving
the `deleteStar G v₀` greedy conditions with `a,b` as sinks. This is the crux-INDEPENDENT
mechanical core of the Lovász ordering; producing `lvl` from 2-connectivity is the (A1) kernel. -/
theorem exists_brooks_rank_of_descent (G : SimpleGraph V) [DecidableRel G.Adj] (v₀ a b : V)
    (hab : a ≠ b) (hnadj : ¬ G.Adj a b) (hva : G.Adj v₀ a) (hvb : G.Adj v₀ b)
    (hreg : ∀ v, G.degree v = 3)
    (lvl : V → ℕ) (hlvl_lt : ∀ x, lvl x < Fintype.card V)
    (hdesc : ∀ u, u ≠ v₀ → u ≠ a → u ≠ b → ¬ G.Adj v₀ u →
        ∃ w, G.Adj u w ∧ w ≠ v₀ ∧ w ≠ a ∧ w ≠ b ∧ lvl w < lvl u) :
    ∃ rank : V → ℕ, Function.Injective rank ∧
      (∀ u, (((deleteStar G v₀).neighborFinset u).filter fun w => rank w < rank u).card < 3) ∧
      (((deleteStar G v₀).neighborFinset a).filter fun w => rank w < rank a).card = 0 ∧
      (((deleteStar G v₀).neighborFinset b).filter fun w => rank w < rank b).card = 0 := by
  classical
  set N := Fintype.card V with hN
  set e : V → ℕ := fun x => (Fintype.equivFin V x : ℕ) with he
  have he_lt : ∀ x, e x < N := fun x => (Fintype.equivFin V x).isLt
  have he_inj : Function.Injective e := by
    intro x y hxy
    exact (Fintype.equivFin V).injective (Fin.val_injective hxy)
  have hv0a : v₀ ≠ a := hva.ne
  have hv0b : v₀ ≠ b := hvb.ne
  set rank : V → ℕ := fun x =>
    if x = a then 0 else if x = b then 1 else N * (N - lvl x) + e x with hrank
  have hra : rank a = 0 := by simp [hrank]
  have hrb : rank b = 1 := by simp [hrank, hab.symm]
  have hrf : ∀ x, x ≠ a → x ≠ b → rank x = N * (N - lvl x) + e x := by
    intro x hxa hxb; simp [hrank, hxa, hxb]
  have hNpos : 0 < N := Fintype.card_pos_iff.mpr ⟨v₀⟩
  have hrf_ge : ∀ x, x ≠ a → x ≠ b → N ≤ rank x := by
    intro x hxa hxb
    rw [hrf x hxa hxb]
    have h1 : 1 ≤ N - lvl x := by have := hlvl_lt x; omega
    calc N = N * 1 := (Nat.mul_one N).symm
      _ ≤ N * (N - lvl x) := by gcongr
      _ ≤ N * (N - lvl x) + e x := Nat.le_add_right _ _
  have hmod : ∀ x, x ≠ a → x ≠ b → rank x % N = e x := by
    intro x hxa hxb
    rw [hrf x hxa hxb, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (he_lt x)
  have hN2 : 2 ≤ N := by
    have h := Finset.card_le_univ ({a, b} : Finset V)
    rw [Finset.card_pair hab] at h
    exact h
  have hinj : Function.Injective rank := by
    intro x y hxy
    by_cases hxa : x = a
    · by_cases hya : y = a
      · rw [hxa, hya]
      · by_cases hyb : y = b
        · rw [hxa, hra, hyb, hrb] at hxy; exact absurd hxy (by norm_num)
        · have := hrf_ge y hya hyb; rw [hxa, hra] at hxy; omega
    · by_cases hxb : x = b
      · by_cases hya : y = a
        · rw [hxb, hrb, hya, hra] at hxy; exact absurd hxy (by norm_num)
        · by_cases hyb : y = b
          · rw [hxb, hyb]
          · have := hrf_ge y hya hyb; rw [hxb, hrb] at hxy; omega
      · by_cases hya : y = a
        · have := hrf_ge x hxa hxb; rw [hya, hra] at hxy; omega
        · by_cases hyb : y = b
          · have := hrf_ge x hxa hxb; rw [hyb, hrb] at hxy; omega
          · have hex : rank x % N = e x := hmod x hxa hxb
            have hey : rank y % N = e y := hmod y hya hyb
            rw [hxy] at hex
            exact he_inj (hex.symm.trans hey)
  have hbcard : ((deleteStar G v₀).neighborFinset b).filter (fun w => rank w < rank b) = ∅ := by
    rw [Finset.filter_eq_empty_iff]; intro w hw
    rw [SimpleGraph.mem_neighborFinset, deleteStar_adj] at hw
    have hwa : w ≠ a := by rintro rfl; exact hnadj hw.1.symm
    rw [hrb]; intro hlt
    by_cases hwb : w = b
    · rw [hwb, hrb] at hlt; omega
    · have := hrf_ge w hwa hwb; omega
  have hacard : ((deleteStar G v₀).neighborFinset a).filter (fun w => rank w < rank a) = ∅ := by
    rw [hra]; apply Finset.filter_false_of_mem; intro w _; omega
  refine ⟨rank, hinj, ?_, ?_, ?_⟩
  · intro u
    by_cases hua : u = a
    · rw [hua, hacard]; simp
    · by_cases hub : u = b
      · rw [hub, hbcard]; simp
      · by_cases huv : u = v₀
        · rw [huv]
          have hemp : (deleteStar G v₀).neighborFinset v₀ = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]; intro w hw
            rw [SimpleGraph.mem_neighborFinset, deleteStar_adj] at hw; exact hw.2.1 rfl
          rw [hemp]; simp
        · rw [deleteStar_neighborFinset G v₀ u huv]
          by_cases hun : G.Adj v₀ u
          · have hmem : v₀ ∈ G.neighborFinset u := by
              rw [SimpleGraph.mem_neighborFinset]; exact hun.symm
            have hcard : ((G.neighborFinset u).erase v₀).card = 2 := by
              rw [Finset.card_erase_of_mem hmem, G.card_neighborFinset_eq_degree, hreg u]
            calc (((G.neighborFinset u).erase v₀).filter (fun w => rank w < rank u)).card
                ≤ ((G.neighborFinset u).erase v₀).card := Finset.card_filter_le _ _
              _ = 2 := hcard
              _ < 3 := by norm_num
          · obtain ⟨w, hadj, hwv, hwa, hwb, hlt⟩ := hdesc u huv hua hub hun
            have hwmem : w ∈ (G.neighborFinset u).erase v₀ := by
              rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]; exact ⟨hwv, hadj⟩
            have hru : rank u = N * (N - lvl u) + e u := hrf u hua hub
            have hrw : rank w = N * (N - lvl w) + e w := hrf w hwa hwb
            have hgt : rank u < rank w := by
              rw [hru, hrw]
              have hstep : (N - lvl u) + 1 ≤ N - lvl w := by have := hlvl_lt u; omega
              calc N * (N - lvl u) + e u
                  < N * (N - lvl u) + N := by have := he_lt u; omega
                _ = N * ((N - lvl u) + 1) := by ring
                _ ≤ N * (N - lvl w) := by gcongr
                _ ≤ N * (N - lvl w) + e w := Nat.le_add_right _ _
            have hwnot : w ∉ ((G.neighborFinset u).erase v₀).filter (fun z => rank z < rank u) := by
              rw [Finset.mem_filter]; rintro ⟨_, hlt2⟩; omega
            have hsub : ((G.neighborFinset u).erase v₀).filter (fun z => rank z < rank u)
                ⊆ ((G.neighborFinset u).erase v₀).erase w := by
              intro z hz
              rw [Finset.mem_erase]
              refine ⟨?_, (Finset.mem_filter.mp hz).1⟩
              rintro rfl; exact hwnot hz
            have hnotmem : v₀ ∉ G.neighborFinset u := by
              rw [SimpleGraph.mem_neighborFinset]; exact fun h => hun h.symm
            have hcard3 : ((G.neighborFinset u).erase v₀).card = 3 := by
              rw [Finset.erase_eq_of_notMem hnotmem, G.card_neighborFinset_eq_degree, hreg u]
            calc (((G.neighborFinset u).erase v₀).filter (fun z => rank z < rank u)).card
                ≤ (((G.neighborFinset u).erase v₀).erase w).card := Finset.card_le_card hsub
              _ = ((G.neighborFinset u).erase v₀).card - 1 := Finset.card_erase_of_mem hwmem
              _ = 2 := by rw [hcard3]
              _ < 3 := by norm_num
  · rw [hacard]; simp
  · rw [hbcard]; simp

omit [DecidableEq V] in
/-- **A1 completion: good triple ⇒ 3-colourable.** If `v₀` has non-adjacent neighbours `a,b`
with `G−{a,b}` (the induced subgraph on `{a,b}ᶜ`) connected, then `G` is 3-colourable: BFS from
`v₀` in `G−{a,b}` yields a level function whose descent feeds `exists_brooks_rank_of_descent` (A2);
colour-controlled greedy gives `c(a)=c(b)=0`, so `v₀` sees ≤2 colours and a free colour extends the
colouring.  The (A1) kernel — the BFS level construction — is carried out below from the graph
distance in `G−{a,b}`, so this theorem is proved unconditionally (no gap remains). -/
theorem colorable_of_good_triple (G : SimpleGraph V) [DecidableRel G.Adj] (v₀ a b : V)
    (hreg : ∀ v, G.degree v = 3)
    (hva : G.Adj v₀ a) (hvb : G.Adj v₀ b) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hgood : (G.induce (({a, b} : Set V)ᶜ)).Connected) : G.Colorable 3 := by
  classical
  obtain ⟨lvl, hlvl_lt, hdesc⟩ :
      ∃ lvl : V → ℕ, (∀ x, lvl x < Fintype.card V) ∧
        (∀ u, u ≠ v₀ → u ≠ a → u ≠ b → ¬ G.Adj v₀ u →
          ∃ w, G.Adj u w ∧ w ≠ v₀ ∧ w ≠ a ∧ w ≠ b ∧ lvl w < lvl u) := by
    let S : Set V := ({a, b} : Set V)ᶜ
    let H : SimpleGraph S := G.induce S
    have hv₀S : v₀ ∈ S := by
      simp only [S, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hva.ne, hvb.ne⟩
    let root : S := ⟨v₀, hv₀S⟩
    let lvl : V → ℕ := fun x => if hx : x ∈ S then H.dist root ⟨x, hx⟩ else 0
    refine ⟨lvl, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ S
      · obtain ⟨p, hp, hplen⟩ := hgood.exists_path_of_dist root ⟨x, hx⟩
        rw [show lvl x = H.dist root ⟨x, hx⟩ by simp [lvl, hx], ← hplen]
        exact lt_of_lt_of_le hp.length_lt
          (Fintype.card_le_of_injective (fun x : S => x.1) Subtype.val_injective)
      · rw [show lvl x = 0 by simp [lvl, hx]]
        exact Fintype.card_pos_iff.mpr ⟨v₀⟩
    · intro u huv hua hub hun
      have huS : u ∈ S := by
        simp only [S, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hua, hub⟩
      have huroot : (⟨u, huS⟩ : S) ≠ root := by
        intro h
        exact huv (congrArg Subtype.val h)
      obtain ⟨w, huw, hwlt⟩ := exists_closer_neighbor H hgood root ⟨u, huS⟩ huroot
      refine ⟨w.1, huw, ?_, ?_, ?_, ?_⟩
      · intro hwv
        apply hun
        have hGuW : G.Adj u w.1 := huw
        rw [hwv] at hGuW
        exact hGuW.symm
      · exact fun hwa => w.property (by simp [S, hwa])
      · exact fun hwb => w.property (by simp [S, hwb])
      · simpa only [lvl, huS, w.property, ↓reduceDIte] using hwlt
  obtain ⟨rank, hrank_inj, hcond, ha0, hb0⟩ :=
    exists_brooks_rank_of_descent G v₀ a b hab hnadj hva hvb hreg lvl hlvl_lt hdesc
  obtain ⟨c', hproper, hctrl⟩ :=
    greedy_coloring_zero (deleteStar G v₀) 3 (by norm_num) rank hrank_inj hcond
  have hca : c' a = ⟨0, by norm_num⟩ := hctrl a ha0
  have hcb : c' b = ⟨0, by norm_num⟩ := hctrl b hb0
  have haN : a ∈ G.neighborFinset v₀ := by rw [SimpleGraph.mem_neighborFinset]; exact hva
  have hbN : b ∈ G.neighborFinset v₀ := by rw [SimpleGraph.mem_neighborFinset]; exact hvb
  have himg : ((G.neighborFinset v₀).image c').card ≤ 2 := by
    have hset : (G.neighborFinset v₀).image c' = ((G.neighborFinset v₀).erase b).image c' := by
      apply Finset.Subset.antisymm
      · intro col hcol
        rw [Finset.mem_image] at hcol ⊢
        obtain ⟨w, hw, rfl⟩ := hcol
        by_cases hwb : w = b
        · exact ⟨a, Finset.mem_erase.mpr ⟨hab, haN⟩, by rw [hca, ← hcb, hwb]⟩
        · exact ⟨w, Finset.mem_erase.mpr ⟨hwb, hw⟩, rfl⟩
      · exact Finset.image_subset_image (Finset.erase_subset _ _)
    rw [hset]
    calc (((G.neighborFinset v₀).erase b).image c').card
        ≤ ((G.neighborFinset v₀).erase b).card := Finset.card_image_le
      _ = G.degree v₀ - 1 := by rw [Finset.card_erase_of_mem hbN, G.card_neighborFinset_eq_degree]
      _ = 2 := by rw [hreg v₀]
  have hfree : ∃ col : Fin 3, col ∉ (G.neighborFinset v₀).image c' := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin 3)) ⊆ (G.neighborFinset v₀).image c' :=
      fun col _ => hcon col
    have hle := Finset.card_le_card hsub
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    omega
  obtain ⟨col₀, hcol₀⟩ := hfree
  refine ⟨⟨Function.update c' v₀ col₀, ?_⟩⟩
  intro x y hxy
  by_cases hxv : x = v₀
  · subst hxv
    have hyv : y ≠ x := (hxy).ne'
    rw [Function.update_self, Function.update_of_ne hyv]
    intro heq
    exact hcol₀ (Finset.mem_image.mpr
      ⟨y, by rw [SimpleGraph.mem_neighborFinset]; exact hxy, heq.symm⟩)
  · by_cases hyv : y = v₀
    · subst hyv
      rw [Function.update_of_ne hxv, Function.update_self]
      intro heq
      exact hcol₀ (Finset.mem_image.mpr
        ⟨x, by rw [SimpleGraph.mem_neighborFinset]; exact hxy.symm, heq⟩)
    · rw [Function.update_of_ne hxv, Function.update_of_ne hyv]
      exact hproper x y ((deleteStar_adj G v₀ x y).mpr ⟨hxy, hxv, hyv⟩)

omit [DecidableEq V] in
/-- **B (reduction, non-2-connected case).** A connected cubic K₄-free graph with no good
triple has a cut vertex and is three-colourable by a cut-vertex/block
reduction. The mechanical and structural halves are fully proved by hand:
`colorable_of_cut_partition` (each component-plus-`x` has `x` at degree `< 3`, so the non-regular
case colours it, and `colorable_glue_at_vertex` merges at `x`), with Lovász cut-existence providing
the cut witness from `¬ ∃ good triple`. -/
theorem colorable_three_cubic_no_good_triple (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : ∀ v, G.degree v = 3) (hK4 : G.CliqueFree 4)
    (hng : ¬ ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b ∧
        (G.induce (({a, b} : Set V)ᶜ)).Connected) : G.Colorable 3 := by
  classical
  obtain ⟨x, d, e, hd, he, hsep⟩ :=
    cut_witness_of_no_good_triple G hconn hreg hK4 hng
  obtain ⟨A₀, B₀, hAne, hBne, hxnA, hxnB, hdisj, hcov, hnocross, hAconn, hBconn⟩ :=
    cut_partition_of_unreachable G hconn x d e hd he hsep
  exact colorable_of_cut_partition G hreg x A₀ B₀ hAne hBne hxnA hxnB hdisj hcov hnocross
    hAconn hBconn

omit [DecidableEq V] in
/-- **B8 (3-regular case).** A connected 3-regular graph with no 4-clique is 3-colourable.
Case split on the existence of a Lovász "good triple" `(v₀,a,b)` with `G−{a,b}` connected:
present ⇒ `colorable_of_good_triple` (A1); absent ⇒ `colorable_three_cubic_no_good_triple` (B). -/
theorem connected_colorable_three_of_degree_eq_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : ∀ v, G.degree v = 3) (hK4 : G.CliqueFree 4) :
    G.Colorable 3 := by
  classical
  by_cases hgt : ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b ∧
      (G.induce (({a, b} : Set V)ᶜ)).Connected
  · obtain ⟨v₀, a, b, hva, hvb, hab, hnadj, hgood⟩ := hgt
    exact colorable_of_good_triple G v₀ a b hreg hva hvb hab hnadj hgood
  · exact colorable_three_cubic_no_good_triple G hconn hreg hK4 hgt

end BrooksSubcubic
end

/- Source unit: LeanPool/BrooksSubcubic/Main.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Subcubic Brooks theorem: Main

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

/-- Brooks' theorem for subcubic graphs: a finite simple graph with maximum degree `≤ 3` and no
4-clique is 3-colourable. -/
theorem brooks_cubic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 3) (hK4 : G.CliqueFree 4) : G.Colorable 3 := by
  classical
  rw [G.colorable_iff_forall_connectedComponent]
  intro c
  let : Fintype c := Fintype.ofFinite c
  let H := c.toSimpleGraph
  let : DecidableRel H.Adj := Classical.decRel _
  have hconn : H.Connected := c.connected_toSimpleGraph
  have hemb : H ↪g G := SimpleGraph.Embedding.induce c.supp
  have hdeg : ∀ v, H.degree v ≤ 3 := by
    intro v
    -- Cardinality is independent of the component's chosen finite enumeration.
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
      Fintype.card_eq_nat_card, H, ConnectedComponent.toSimpleGraph] using
      (induce_degree_le G c.supp v).trans ((G.degree_le_maxDegree v.val).trans hΔ)
  have hfree : H.CliqueFree 4 := hK4.comap ⟨hemb.toCopy⟩
  by_cases hlow : ∃ v, H.degree v < 3
  · exact connected_colorable_three_of_exists_degree_lt H hconn hdeg hlow
  · apply connected_colorable_three_of_degree_eq_three H hconn _ hfree
    intro v
    exact Nat.le_antisymm (hdeg v) (not_lt.mp (not_exists.mp hlow v))

end BrooksSubcubic
end
