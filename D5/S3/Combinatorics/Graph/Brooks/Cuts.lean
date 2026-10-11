/- GID: D5/S3/Combinatorics/Graph/Brooks/Cuts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Brooks/Cuts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic.Push]
   utility: none
   digest: Licensed cut and attachment structure for the subcubic Brooks theorem. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Push
import D5.S3.Combinatorics.Graph.Brooks.Coloring

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

/- Source unit: LeanPool/BrooksSubcubic/ComponentAttachments.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Subcubic Brooks theorem: ComponentAttachments

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- If `W` is closed under `G`-adjacency, a walk starting in `W` stays in `W`. -/
theorem mem_of_walk_closed (G : SimpleGraph V) (W : Set V)
    (hW : ∀ w ∈ W, ∀ y, G.Adj w y → y ∈ W) {u v : V} (p : G.Walk u v) :
    u ∈ W → v ∈ W := by
  classical
  induction p with
  | nil => exact id
  | @cons a b c hadj q ih => exact fun ha => ih (hW a ha b hadj)

omit [Fintype V] in
/-- **Linchpin.** In a connected `G`, for any `d ≠ x`, `x` is adjacent to some vertex `z` in the
same `G−x`-component as `d`. -/
theorem exists_adj_in_class (G : SimpleGraph V) (hconn : G.Connected)
    {x d : V} (hd : d ≠ x) :
    ∃ z, G.Adj x z ∧ ∃ hz : z ≠ x,
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨d, hd⟩ =
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨z, hz⟩ := by
  classical
  by_contra hcon
  push Not at hcon
  set D := (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨d, hd⟩ with hD
  set W : Set V := {v | ∃ hv : v ≠ x,
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨v, hv⟩ = D} with hWdef
  have hdW : d ∈ W := ⟨hd, rfl⟩
  have hxW : x ∉ W := by rintro ⟨hx, _⟩; exact hx rfl
  have hclosed : ∀ w ∈ W, ∀ y, G.Adj w y → y ∈ W := by
    rintro w ⟨hwx, hwD⟩ y hadj
    by_cases hyx : y = x
    · subst hyx
      exact absurd (hwD ▸ rfl) (hcon w hadj.symm hwx)
    · refine ⟨hyx, ?_⟩
      have hadj' : (G.induce ({x}ᶜ : Set V)).Adj ⟨w, hwx⟩ ⟨y, hyx⟩ := by
        simpa [SimpleGraph.induce, SimpleGraph.comap] using hadj
      rw [← hwD]
      exact (ConnectedComponent.eq.mpr hadj'.reachable).symm
  obtain ⟨p⟩ := hconn.preconnected d x
  exact hxW (mem_of_walk_closed G W hclosed p hdW)

end BrooksSubcubic
end

/- Source unit: LeanPool/BrooksSubcubic/CandidatePair.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Subcubic Brooks theorem: CandidatePair

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- **P2 (distance-2 candidate).** In a connected `G`, if `x` has a non-neighbour `w ≠ x`, then `x`
has a neighbour `u` which has a neighbour `b` with `¬ G.Adj x b` and `b ≠ x`. (I.e. a vertex `b` at
distance 2 from `x`, with common neighbour `u`.) Proof: the set `{x} ∪ N(x)` is not closed under
adjacency (it omits `w` yet `x` reaches `w`), so some neighbour of `x` has an edge leaving it. -/
theorem exists_dist2_pair (G : SimpleGraph V) (hconn : G.Connected)
    {x w : V} (hwx : w ≠ x) (hxw : ¬ G.Adj x w) :
    ∃ u b, G.Adj x u ∧ G.Adj u b ∧ ¬ G.Adj x b ∧ b ≠ x := by
  classical
  set S : Set V := {y | y = x ∨ G.Adj x y} with hSdef
  have hxS : x ∈ S := Or.inl rfl
  have hwS : w ∉ S := by
    intro hmem; rcases hmem with heq | hadj
    · exact hwx heq
    · exact hxw hadj
  have hnotclosed : ¬ ∀ s ∈ S, ∀ y, G.Adj s y → y ∈ S := by
    intro hcl
    obtain ⟨p⟩ := hconn.preconnected x w
    exact hwS (mem_of_walk_closed G S hcl p hxS)
  push Not at hnotclosed
  obtain ⟨s, hsS, y, hsy, hyS⟩ := hnotclosed
  have hyx : y ≠ x := by rintro rfl; exact hyS (Or.inl rfl)
  have hxy : ¬ G.Adj x y := fun h => hyS (Or.inr h)
  rcases hsS with rfl | hxs
  · exact absurd hsy hxy
  · exact ⟨s, y, hxs, hsy, hxy, hyx⟩

end BrooksSubcubic
end

/- Source unit: LeanPool/BrooksSubcubic/CutVertex.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Subcubic Brooks theorem: CutVertex

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

/-- `x` is a cut vertex of `G` when deleting it disconnects `G`. -/
def IsCutVertex (G : SimpleGraph V) (x : V) : Prop :=
  ¬ (G.induce ({x}ᶜ : Set V)).Connected

omit [Fintype V] in
/-- A cut vertex with nonempty complement yields two mutually unreachable vertices. -/
theorem exists_unreachable_of_cutVertex (G : SimpleGraph V) (x : V)
    (w : V) (hw : w ≠ x) (hcut : IsCutVertex G x) :
    ∃ (d e : V) (hd : d ≠ x) (he : e ≠ x),
      ¬ (G.induce ({x}ᶜ : Set V)).Reachable ⟨d, hd⟩ ⟨e, he⟩ := by
  classical
  have hwmem : w ∈ ({x}ᶜ : Set V) := by simpa using hw
  have : Nonempty ↥({x}ᶜ : Set V) := ⟨⟨w, hwmem⟩⟩
  have hnp : ¬ (G.induce ({x}ᶜ : Set V)).Preconnected := by
    intro hp
    exact hcut ((SimpleGraph.connected_iff _).mpr ⟨hp, inferInstance⟩)
  simp only [SimpleGraph.Preconnected, not_forall] at hnp
  obtain ⟨u, v, huv⟩ := hnp
  exact ⟨u.val, v.val, u.property, v.property, huv⟩

omit [Fintype V] in
/-- If deleting a set `S` disconnects `G` (and `Sᶜ` is nonempty via
`w ∉ S`), there are two vertices outside `S` that are mutually unreachable in `G − S`. The 2-cut
case `S = {a₀, y}` feeds the endblock analysis of Lovász Case 2. -/
theorem exists_unreachable_of_notConnected (G : SimpleGraph V)
    (S : Set V) (w : V) (hw : w ∉ S)
    (hdis : ¬ (G.induce (Sᶜ : Set V)).Connected) :
    ∃ (d e : V) (hd : d ∉ S) (he : e ∉ S),
      ¬ (G.induce (Sᶜ : Set V)).Reachable ⟨d, hd⟩ ⟨e, he⟩ := by
  classical
  have : Nonempty ↥(Sᶜ : Set V) := ⟨⟨w, hw⟩⟩
  have hnp : ¬ (G.induce (Sᶜ : Set V)).Preconnected := by
    intro hp
    exact hdis ((SimpleGraph.connected_iff _).mpr ⟨hp, inferInstance⟩)
  simp only [SimpleGraph.Preconnected, not_forall] at hnp
  obtain ⟨u, v, huv⟩ := hnp
  exact ⟨u.val, v.val, u.property, v.property, huv⟩

omit [Fintype V] in
/-- **`a₀` reaches every component of `G−{a₀,y}`.** If `G−y` is connected and `a₀ ≠ y`, then for
every `d ∉ {a₀,y}`, `a₀` has a neighbour in `d`'s `G−{a₀,y}`-component. (In `H = G−y`, `a₀` is a
cut vertex and every component of `H−a₀ = G−{a₀,y}` hangs off `a₀`.) This yields the candidate pair
`a,b ∈ N(a₀)` in two distinct components for Lovász Case 2. -/
theorem a0_adj_component (G : SimpleGraph V)
    {a0 y : V} (hay : a0 ≠ y) (hHconn : (G.induce ({y}ᶜ : Set V)).Connected)
    {d : V} (hd : d ∈ (({a0, y} : Set V)ᶜ)) :
    ∃ (z : V) (hz : z ∈ (({a0, y} : Set V)ᶜ)), G.Adj a0 z ∧
      (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ =
      (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨z, hz⟩ := by
  classical
  by_contra hcon
  push Not at hcon
  set D := (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ with hDdef
  set W : Set V := {v | ∃ hv : v ∈ (({a0, y} : Set V)ᶜ),
      (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨v, hv⟩ = D} with hWdef
  have hdy : d ≠ y := fun h => hd (by rw [h]; exact Or.inr rfl)
  have hay' : a0 ≠ y := hay
  set W' : Set ↥({y}ᶜ : Set V) := {v' | v'.val ∈ W} with hW'def
  have hdmem : d ∈ ({y}ᶜ : Set V) := hdy
  have hdW' : (⟨d, hdmem⟩ : ↥({y}ᶜ : Set V)) ∈ W' := ⟨hd, rfl⟩
  have hamem : a0 ∈ ({y}ᶜ : Set V) := hay'
  have haW' : (⟨a0, hamem⟩ : ↥({y}ᶜ : Set V)) ∉ W' := by
    rintro ⟨hv, _⟩
    exact hv (Or.inl rfl)
  have hclosed : ∀ w' ∈ W', ∀ z', (G.induce ({y}ᶜ : Set V)).Adj w' z' → z' ∈ W' := by
    rintro w' ⟨hwS, hwD⟩ z' hadj
    have hadjG : G.Adj w'.val z'.val := by
      simpa [SimpleGraph.induce, SimpleGraph.comap] using hadj
    have hz'y : z'.val ≠ y := z'.property
    by_cases hz'a0 : z'.val = a0
    · -- a0 adjacent to w'.val ∈ D's class ⇒ contradicts hcon
      exfalso
      have : G.Adj a0 w'.val := by rw [← hz'a0]; exact hadjG.symm
      exact (hcon w'.val hwS this) hwD.symm
    · have hz'mem : z'.val ∈ (({a0, y} : Set V)ᶜ) := by
        intro hmem; rcases hmem with h | h
        · exact hz'a0 h
        · exact hz'y h
      refine ⟨hz'mem, ?_⟩
      have hadj' : (G.induce (({a0, y} : Set V)ᶜ)).Adj ⟨w'.val, hwS⟩ ⟨z'.val, hz'mem⟩ := by
        simpa [SimpleGraph.induce, SimpleGraph.comap] using hadjG
      rw [← hwD]
      exact (ConnectedComponent.eq.mpr hadj'.reachable).symm
  obtain ⟨p⟩ := hHconn.preconnected ⟨d, hdmem⟩ ⟨a0, hamem⟩
  exact haW' (mem_of_walk_closed _ W' hclosed p hdW')

end BrooksSubcubic
end

/- Source unit: LeanPool/BrooksSubcubic/CutPartition.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Subcubic Brooks theorem: CutPartition

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A union of components of the vertex-deleted graph, each attached to the deleted vertex,
becomes connected when that vertex is inserted. -/
lemma connected_induce_insert_of_component_neighbors (G : SimpleGraph V)
    (x : V) (A : Finset V)
    (P : (G.induce ({x}ᶜ : Set V)).ConnectedComponent → Prop)
    (hmem : ∀ v, v ∈ A ↔ ∃ hv : v ≠ x,
      P ((G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨v, hv⟩))
    (hneigh : ∀ C, P C → ∃ z, G.Adj x z ∧ ∃ hz : z ≠ x,
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨z, hz⟩ = C) :
    (G.induce ((insert x A : Finset V) : Set V)).Connected := by
  classical
  have hx_reach : ∀ (v : V) (hv : v ∈ A),
      (G.induce (↑(insert x A))).Reachable ⟨x, by simp⟩ ⟨v, by simp [hv]⟩ := by
    intro v hvA
    obtain ⟨hvx, hPC⟩ := (hmem v).mp hvA
    obtain ⟨z, hxz, hzx, hzcomp⟩ := hneigh _ hPC
    have hzA : z ∈ A := (hmem z).mpr ⟨hzx, hzcomp ▸ hPC⟩
    obtain ⟨p⟩ := ConnectedComponent.eq.mp hzcomp
    have hpA : ∀ w ∈ p.support, w.val ∈ A := by
      intro w hw
      apply (hmem w.val).mpr
      refine ⟨w.property, ?_⟩
      have hcomp := ConnectedComponent.eq.mpr (p.takeUntil w hw).reachable
      rw [← hcomp, hzcomp]
      exact hPC
    let q := p.map (Embedding.induce ({x}ᶜ : Set V)).toHom
    have hq : ∀ w ∈ q.support, w ∈ (↑(insert x A) : Set V) := by
      intro w hw
      change w ∈ (p.map (Embedding.induce ({x}ᶜ : Set V)).toHom).support at hw
      rw [SimpleGraph.Walk.support_map] at hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      exact Finset.mem_insert_of_mem (hpA w' hw')
    have hzv : (G.induce (↑(insert x A))).Reachable
        ⟨z, by simp [hzA]⟩ ⟨v, by simp [hvA]⟩ := ⟨q.induce _ hq⟩
    exact (show (G.induce (↑(insert x A))).Adj
      ⟨x, by simp⟩ ⟨z, by simp [hzA]⟩ from hxz).reachable.trans hzv
  rw [connected_iff]
  constructor
  · rintro ⟨u, hu⟩ ⟨v, hv⟩
    simp only [Finset.mem_insert, Finset.mem_coe] at hu hv
    rcases hu with rfl | huA <;> rcases hv with rfl | hvA
    · exact Reachable.rfl
    · exact hx_reach v hvA
    · exact (hx_reach u huA).symm
    · exact (hx_reach u huA).symm.trans (hx_reach v hvA)
  · exact ⟨⟨x, by simp⟩⟩

theorem cut_partition_of_unreachable (G : SimpleGraph V)
    (hconn : G.Connected) (x d e : V) (hd : d ≠ x) (he : e ≠ x)
    (hsep : ¬ (G.induce ({x}ᶜ : Set V)).Reachable ⟨d, hd⟩ ⟨e, he⟩) :
    ∃ (A₀ B₀ : Finset V), A₀.Nonempty ∧ B₀.Nonempty ∧ x ∉ A₀ ∧ x ∉ B₀ ∧
      Disjoint A₀ B₀ ∧ insert x (A₀ ∪ B₀) = Finset.univ ∧
      (∀ a ∈ A₀, ∀ b ∈ B₀, ¬ G.Adj a b) ∧
      (G.induce ((insert x A₀ : Finset V) : Set V)).Connected ∧
      (G.induce ((insert x B₀ : Finset V) : Set V)).Connected := by
  classical
  let preB₀ : Finset {v : V // v ≠ x} :=
    Finset.univ.filter (fun v => (G.induce ({x}ᶜ : Set V)).Reachable ⟨e, he⟩ v)
  let B₀ : Finset V := preB₀.map ⟨Subtype.val, Subtype.val_injective⟩
  let A₀ : Finset V := (Finset.univ \ {x}) \ B₀
  have hB₀_mem : ∀ v, v ∈ B₀ ↔ ∃ (w : {v : V // v ≠ x}), w ∈ preB₀ ∧ w.val = v :=
    fun v => Finset.mem_map
  have hA₀_mem : ∀ v, v ∈ A₀ ↔ v ≠ x ∧ v ∉ B₀ := fun v => by simp [A₀]
  refine ⟨A₀, B₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · use d
    simp only [hA₀_mem]
    refine ⟨hd, ?_⟩
    simp only [hB₀_mem]
    intro ⟨w, hw_mem, hw_eq⟩
    simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and] at hw_mem
    have hw_eq' : w = ⟨d, hd⟩ := Subtype.ext hw_eq
    rw [hw_eq'] at hw_mem
    exact hsep hw_mem.symm
  · use e
    simp only [hB₀_mem]
    use ⟨e, he⟩
    simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    exact SimpleGraph.Reachable.rfl
  · rw [hA₀_mem]
    simp
  · rw [hB₀_mem]
    intro ⟨w, _, hw_eq⟩
    have : w.val = x := hw_eq
    exact w.property this
  · rw [Finset.disjoint_left]
    intro a haA haB
    rw [hA₀_mem] at haA
    exact haA.2 haB
  · ext v
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hvx : v = x
    case pos => left; exact hvx
    case neg =>
      by_cases hvB₀ : v ∈ B₀
      · right; exact Or.inr hvB₀
      · right
        rw [hA₀_mem]
        exact Or.inl ⟨hvx, hvB₀⟩
  · intro a haA b hbB hab
    rw [hA₀_mem] at haA
    rw [hB₀_mem] at hbB
    obtain ⟨⟨vb, hvb⟩, hve_mem, hvb_eq⟩ := hbB
    simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and] at hve_mem
    have h_a_in_B₀ : a ∈ B₀ := by
      rw [hB₀_mem]
      use ⟨a, haA.1⟩
      simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      have hb_eq : b = vb := hvb_eq.symm
      have hab' : (G.induce ({x}ᶜ : Set V)).Adj ⟨a, haA.1⟩ ⟨vb, hvb⟩ := by
        rw [hb_eq] at hab
        change G.Adj a vb
        exact hab
      exact SimpleGraph.Reachable.trans hve_mem hab'.reachable.symm
    exact haA.2 h_a_in_B₀
  · apply connected_induce_insert_of_component_neighbors G x A₀
      (fun C => C ≠ (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨e, he⟩)
    · intro v
      rw [hA₀_mem]
      apply Iff.intro
      · intro ⟨hvx, hvB₀⟩
        refine ⟨hvx, ?_⟩
        intro h
        apply hvB₀
        apply (hB₀_mem v).mpr
        refine ⟨⟨v, hvx⟩, ?_, rfl⟩
        simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ConnectedComponent.eq.mp h.symm
      · intro ⟨hvx, hPC⟩
        refine ⟨hvx, ?_⟩
        intro hvB₀
        rw [hB₀_mem] at hvB₀
        obtain ⟨w, hw_mem, hw_eq⟩ := hvB₀
        simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and] at hw_mem
        have h_mk_eq : (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨e, he⟩ =
            (G.induce ({x}ᶜ : Set V)).connectedComponentMk w :=
          ConnectedComponent.eq.mpr hw_mem
        have hw_eq' : w = (⟨v, hvx⟩ : {v : V // v ≠ x}) := Subtype.ext hw_eq
        rw [hw_eq'] at h_mk_eq
        exact hPC h_mk_eq.symm
    · intro C hC
      obtain ⟨⟨v, hv⟩, hv_rep⟩ := C.exists_rep
      have hvx : v ≠ x := hv
      have hC_eq : C = (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨v, hvx⟩ := by
        rw [← hv_rep]
        rfl
      obtain ⟨z, hzx, hzx_ne, hz_comp⟩ := exists_adj_in_class G hconn hvx
      refine ⟨z, hzx, hzx_ne, ?_⟩
      exact Eq.trans hz_comp.symm hC_eq.symm
  · apply connected_induce_insert_of_component_neighbors G x B₀
      (fun C => C = (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨e, he⟩)
    · intro v
      rw [hB₀_mem]
      constructor
      · rintro ⟨⟨w, hw⟩, hw_mem, hw_eq⟩
        simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and] at hw_mem
        have hw_ne : v ≠ x := hw_eq ▸ hw
        refine ⟨hw_ne, ?_⟩
        simp only [← hw_eq]
        exact (ConnectedComponent.eq.mpr hw_mem.symm)
      · rintro ⟨hvx, hPC⟩
        use ⟨v, hvx⟩
        simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact (ConnectedComponent.eq.mp hPC).symm
    · intro C hCeq
      rw [hCeq]
      obtain ⟨z, hzx, hzx_ne, hz_comp⟩ := exists_adj_in_class G hconn he
      exact ⟨z, hzx, hzx_ne, hz_comp.symm⟩

end BrooksSubcubic
end
