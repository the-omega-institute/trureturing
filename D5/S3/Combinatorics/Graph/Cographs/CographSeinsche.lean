/- GID: D5/S3/Combinatorics/Graph/Cographs/CographSeinsche
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Cographs/CographSeinsche
   mirror-E: none
   anchors: []
   utility: none
   digest: Native induced path exclusion and Seinsche's component cut. -/

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Authors: Juan Pablo Traverso Gianini
Released under Apache 2.0 license as described in the repository LICENSE.
Lean Pool attribution is in docs/reports/licenses/lean-pool-structural-graph-classes-NOTICE.txt.

Adapted from LeanPool/StructuralGraphClasses/{PathFour,InducedPathFour,CographDecomposition}
at https://github.com/LeanPool/lean-pool/tree/256b14819101d37112f04af6001efb73a4f3314d.
The original modules are combined here behind one D5 import. Retire this port when the
pinned Mathlib supplies the native induced-P₄ bridge and Seinsche decomposition.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card

/-!
# Seinsche's decomposition theorem

D. Seinsche, *On a property of the class of n-colorable graphs*, JCTB 16(2),
191–193, https://doi.org/10.1016/0095-8956(74)90063-X.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V}

/-- There is no induced path on four vertices, in the order `a, b, c, d`. -/
def IsP4Free (G : SimpleGraph V) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
    ¬G.Adj a c → ¬G.Adj a d → ¬G.Adj b d → False

/-- Four-vertex path exclusion pulls back along vertex maps. -/
theorem IsP4Free.comap (h : G.IsP4Free) (f : W → V) : (G.comap f).IsP4Free := by
  intro a b c d hab hbc hcd hac had hbd
  exact h (f a) (f b) (f c) (f d) hab hbc hcd hac had hbd

/-- Every induced subgraph of a graph excluding `P₄` also excludes `P₄`. -/
theorem IsP4Free.induce (h : G.IsP4Free) (s : Set V) : (G.induce s).IsP4Free :=
  h.comap Subtype.val

/-- The complement of an induced `P₄` is another induced `P₄`. -/
theorem IsP4Free.compl (h : G.IsP4Free) : Gᶜ.IsP4Free := by
  intro a b c d hab hbc hcd hac had hbd
  rw [G.compl_adj] at hab hbc hcd
  have hac' : G.Adj a c := by
    by_contra hn
    apply hac
    refine ⟨?_, hn⟩
    intro heq
    subst c
    exact had hcd
  have had' : G.Adj a d := by
    by_contra hn
    apply had
    refine ⟨?_, hn⟩
    intro heq
    subst d
    exact hac ⟨hcd.1.symm, fun he => hcd.2 he.symm⟩
  have hbd' : G.Adj b d := by
    by_contra hn
    apply hbd
    refine ⟨?_, hn⟩
    intro heq
    subst d
    exact had hab
  exact h c a d b hac'.symm had' hbd'.symm
    (fun he => hcd.2 he) (fun he => hbc.2 he.symm) hab.2

end SimpleGraph


namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The local `P₄` exclusion predicate excludes native induced path embeddings. -/
theorem IsP4Free.not_pathGraph_four_isIndContained (h : G.IsP4Free) :
    ¬(pathGraph 4).IsIndContained G := by
  rintro ⟨f⟩
  apply h (f 0) (f 1) (f 2) (f 3)
  · exact f.map_adj_iff.mpr (by simp [pathGraph_adj])
  · exact f.map_adj_iff.mpr (by simp [pathGraph_adj])
  · exact f.map_adj_iff.mpr (by simp [pathGraph_adj])
  · intro he
    simpa [pathGraph_adj] using f.map_adj_iff.mp he
  · intro he
    simpa [pathGraph_adj] using f.map_adj_iff.mp he
  · intro he
    simpa [pathGraph_adj] using f.map_adj_iff.mp he

/-- Four vertices satisfying the path edges and nonedges give a native induced embedding. -/
theorem pathGraph_four_isIndContained_of_adj {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hac : ¬G.Adj a c) (had : ¬G.Adj a d) (hbd : ¬G.Adj b d) :
    (pathGraph 4).IsIndContained G := by
  have habNe := hab.ne
  have hbcNe := hbc.ne
  have hcdNe := hcd.ne
  have hacNe : a ≠ c := by
    rintro rfl
    exact had hcd
  have hadNe : a ≠ d := by
    rintro rfl
    exact hbd hab.symm
  have hbdNe : b ≠ d := by
    rintro rfl
    exact had hab
  let f : Fin 4 → V := ![a, b, c, d]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  refine ⟨⟨⟨f, hf⟩, ?_⟩⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [f, pathGraph_adj, hab, hbc, hcd, hac, had, hbd, G.adj_comm]

/-- Local path exclusion and native induced-path exclusion are equivalent, without finiteness. -/
theorem isP4Free_iff_not_pathGraph_four_isIndContained :
    G.IsP4Free ↔ ¬(pathGraph 4).IsIndContained G := by
  refine ⟨IsP4Free.not_pathGraph_four_isIndContained, ?_⟩
  intro h a b c d hab hbc hcd hac had hbd
  exact h (pathGraph_four_isIndContained_of_adj hab hbc hcd hac had hbd)

end SimpleGraph


namespace SimpleGraph

universe u

variable {V : Type*} {G : SimpleGraph V}

/-- Every component after deletion meets the neighborhood of the deleted vertex. -/
theorem Preconnected.exists_neighbor_in_deleted_component (hc : G.Preconnected)
    (v : V) (x : {u : V // u ≠ v}) :
    ∃ y : {u : V // u ≠ v}, (G.induce {u | u ≠ v}).Reachable x y ∧ G.Adj v y := by
  classical
  let H := G.induce {u | u ≠ v}
  let S : Set V := {u | ∃ hu : u ≠ v, H.Reachable x ⟨u, hu⟩}
  obtain ⟨p⟩ := hc x.val v
  have hx : x.val ∈ S := ⟨x.property, Reachable.refl x⟩
  have hv : v ∉ S := by rintro ⟨hne, _⟩; exact hne rfl
  obtain ⟨d, _, hdS, hdOut⟩ := p.exists_boundary_dart S hx hv
  obtain ⟨hdv, hdReach⟩ := hdS
  have hend : d.snd = v := by
    by_contra hn
    apply hdOut
    exact ⟨hn, hdReach.trans (Adj.reachable (show H.Adj ⟨d.fst, hdv⟩ ⟨d.snd, hn⟩
      from d.adj))⟩
  refine ⟨⟨d.fst, hdv⟩, hdReach, ?_⟩
  simpa only [hend] using d.adj.symm

/-- An outside neighbor prevents a change of adjacency to the deleted vertex
along a connected component: such a change would form an induced `P₄`. -/
theorem IsP4Free.adj_of_deleted_reachable (hp : G.IsP4Free) (v : V)
    (x y z : {u : V // u ≠ v})
    (hxy : (G.induce {u | u ≠ v}).Reachable x y)
    (hxz : ¬(G.induce {u | u ≠ v}).Reachable x z)
    (hvx : G.Adj v x) (hvz : G.Adj v z) : G.Adj v y := by
  let H := G.induce {u | u ≠ v}
  have hr := (H.reachable_iff_reflTransGen x y).mp hxy
  induction hr with
  | refl => exact hvx
  | @tail a b hab hadj ih =>
    have hx_a : H.Reachable x a := (H.reachable_iff_reflTransGen x a).mpr hab
    have haz : ¬G.Adj a.val z.val := by
      intro h
      exact hxz (hx_a.trans (Adj.reachable (show H.Adj a z from h)))
    have hbz : ¬G.Adj b.val z.val := by
      intro h
      exact hxz (hx_a.trans hadj.reachable |>.trans
        (Adj.reachable (show H.Adj b z from h)))
    by_contra hvb
    exact hp b.val a.val v z.val hadj.symm (ih hx_a).symm hvz
      (fun h => hvb h.symm) hbz haz

/-- A disconnected vertex deletion in a connected `P₄`-free graph makes the
deleted vertex universal. No finiteness hypothesis is needed. -/
theorem IsP4Free.adj_all_of_not_preconnected_delete (hp : G.IsP4Free)
    (hc : G.Preconnected) (v : V)
    (hd : ¬(G.induce {u | u ≠ v}).Preconnected) : ∀ x, x ≠ v → G.Adj v x := by
  classical
  let H := G.induce {u | u ≠ v}
  have hd' : ¬∀ a b, H.Reachable a b := hd
  obtain ⟨a, ha⟩ := not_forall.mp hd'
  obtain ⟨b, hab⟩ := not_forall.mp ha
  intro x hx
  let x' : {u : V // u ≠ v} := ⟨x, hx⟩
  have hout : ∃ z, ¬H.Reachable x' z := by
    by_cases hxa : H.Reachable x' a
    · exact ⟨b, fun hxb => hab (hxa.symm.trans hxb)⟩
    · exact ⟨a, hxa⟩
  obtain ⟨z, hxz⟩ := hout
  obtain ⟨y, hxy, hvy⟩ := hc.exists_neighbor_in_deleted_component v x'
  obtain ⟨w, hzw, hvw⟩ := hc.exists_neighbor_in_deleted_component v z
  have hyw : ¬H.Reachable y w := by
    intro h
    exact hxz (hxy.trans h |>.trans hzw.symm)
  exact hp.adj_of_deleted_reachable v y x' w hxy.symm hyw hvy hvw

/-- A universal vertex is isolated in the complement, so that complement cannot
be preconnected when there is another vertex. -/
theorem not_preconnected_compl_of_universal [Nontrivial V] (v : V)
    (hv : ∀ x, x ≠ v → G.Adj v x) : ¬Gᶜ.Preconnected := by
  intro hc
  obtain ⟨x, hx⟩ := hc.exists_adj_of_nontrivial v
  exact hx.2 (hv x hx.1.symm)

/-- Complementation commutes with induced restriction. -/
theorem compl_induce_eq_induce_compl (s : Set V) : (G.induce s)ᶜ = Gᶜ.induce s := by
  ext a b
  simp [compl_adj, Subtype.ext_iff]

private theorem not_both_preconnected_of_card_le (n : ℕ) :
    ∀ (W : Type u) [Fintype W] [Nontrivial W] (H : SimpleGraph W),
      Fintype.card W ≤ n → H.IsP4Free → H.Preconnected → ¬Hᶜ.Preconnected := by
  classical
  induction n with
  | zero =>
    intro W _ _ H hcard hp hc hcc
    have : 0 < Fintype.card W := Fintype.card_pos
    omega
  | succ n ih =>
    intro W _ _ H hcard hp hc hcc
    let v : W := Classical.arbitrary W
    let D := {x : W // x ≠ v}
    let K := H.induce {x | x ≠ v}
    have hsmall : Fintype.card D ≤ n := by
      have : Fintype.card D < Fintype.card W :=
        Fintype.card_lt_of_injective_of_notMem (f := fun x : D => x.val) (b := v)
          Subtype.val_injective (by rintro ⟨x, hx⟩; exact x.property hx)
      omega
    have hk : K.Preconnected := by
      by_contra hn
      exact not_preconnected_compl_of_universal v
        (hp.adj_all_of_not_preconnected_delete hc v hn) hcc
    have hkc : Kᶜ.Preconnected := by
      have hdel : (Hᶜ.induce {x | x ≠ v}).Preconnected := by
        by_contra hn
        have hall := hp.compl.adj_all_of_not_preconnected_delete hcc v hn
        have hnot := not_preconnected_compl_of_universal v hall
        exact hnot (by simpa only [compl_compl] using hc)
      rwa [compl_induce_eq_induce_compl]
    by_cases hs : Subsingleton D
    · let _ := hs
      obtain ⟨y, hy⟩ := hc.exists_adj_of_nontrivial v
      have hall : ∀ x, x ≠ v → H.Adj v x := by
        intro x hx
        have he : (⟨y, hy.ne.symm⟩ : D) = ⟨x, hx⟩ := Subsingleton.elim _ _
        have hev : y = x := congrArg Subtype.val he
        simpa only [hev] using hy
      exact not_preconnected_compl_of_universal v hall hcc
    · let _ : Nontrivial D := not_subsingleton_iff_nontrivial.mp hs
      exact ih D K hsmall (hp.induce {x | x ≠ v}) hk hkc

/-- Seinsche's decomposition theorem: a nontrivial finite `P₄`-free graph is
disconnected or has disconnected complement. -/
theorem IsP4Free.not_preconnected_or_compl [Finite V] [Nontrivial V]
    (hp : G.IsP4Free) : ¬G.Preconnected ∨ ¬Gᶜ.Preconnected := by
  classical
  let _ := Fintype.ofFinite V
  by_cases hc : G.Preconnected
  · exact Or.inr (not_both_preconnected_of_card_le (Fintype.card V) V G le_rfl hp hc)
  · exact Or.inl hc

end SimpleGraph
