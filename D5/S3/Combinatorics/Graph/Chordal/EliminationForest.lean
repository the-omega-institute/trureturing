/- GID: D5/S3/Combinatorics/Graph/Chordal/EliminationForest
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/EliminationForest
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simplicial elimination gives ranks and a rooted clique forest. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac
import Mathlib.ModelTheory.Graph

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-!
Adapted from LeanPool/lean-pool at edbe5bd56f476cc2965564676b66199f281ab714.
Source paths and the original proof attributions are specified in
Library/GraphInvariants/traversogianini2026brooks.md.
The complete Apache-2.0 LICENSE and upstream NOTICE are retained in
docs/reports/brooks-suppliers/lean-pool-LICENSE.txt and lean-pool-NOTICE.txt.
Modifications: repository imports and ordinary Lean sections replace the donor
module interface; only the dependencies of the finite PEO characterization are
retained, with pinned Mathlib walk and relation suppliers used directly.
Retirement requires an equivalent complete characterization in the host's
pinned Mathlib, correspondence to the native predicate, and migrated consumers.
-/

/-! # Elimination orders and rooted clique forests

Parents are Option-valued so empty and disconnected graphs require no extra node.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A **clique tree** (rooted clique forest) of `G` indexed by `ι`.

`bag i` are cliques of `G` covering all vertices and all edges; `parent` organises the nodes into
a rooted forest (made acyclic by the strictly decreasing `rank`); `top v` is the highest node whose
bag contains `v`, and `mem_bag_parent` is the local form of the running-intersection property: a
bag containing `v` which is not `top v` passes `v` on to its parent. -/
structure CliqueTree (G : SimpleGraph V) (ι : Type*) where
  /-- The bag (clique) attached to a node. -/
  bag : ι → Finset V
  /-- The parent of a node, `none` at a root. -/
  parent : ι → Option ι
  /-- A rank witnessing acyclicity; it also distinguishes nodes. -/
  rank : ι → ℕ
  /-- The top node of a vertex: the highest bag containing it. -/
  top : V → ι
  /-- Distinct nodes have distinct ranks. -/
  rank_injective : Function.Injective rank
  /-- The rank strictly decreases towards the root. -/
  rank_parent_lt : ∀ {i j}, parent i = some j → rank j < rank i
  /-- Every bag is a clique. -/
  bag_isClique : ∀ i, G.IsClique (bag i : Set V)
  /-- Every vertex lies in its own top bag. -/
  mem_bag_top : ∀ v, v ∈ bag (top v)
  /-- Every edge lies in some bag. -/
  exists_bag_of_adj : ∀ {u v}, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  /-- Local running-intersection property. -/
  mem_bag_parent : ∀ {i v}, v ∈ bag i → i ≠ top v → ∃ j, parent i = some j ∧ v ∈ bag j

namespace CliqueTree

variable {ι : Type*} (T : CliqueTree G ι)

/-- `T.IsAncestor i j` means that `j` occurs on the chain of parents starting at `i`
(inclusively). -/
def IsAncestor (i j : ι) : Prop := Relation.ReflTransGen (fun a b => T.parent a = some b) i j

variable {T}

@[refl] theorem isAncestor_refl (i : ι) : T.IsAncestor i i := Relation.ReflTransGen.refl

theorem IsAncestor.rank_le {i j : ι} (h : T.IsAncestor i j) : T.rank j ≤ T.rank i := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans (le_of_lt (T.rank_parent_lt hbc)) ih

/-- The ancestor relation is antisymmetric. -/
theorem IsAncestor.antisymm {i j : ι} (h₁ : T.IsAncestor i j) (h₂ : T.IsAncestor j i) : i = j :=
  T.rank_injective (le_antisymm h₂.rank_le h₁.rank_le)

/-- Ancestors of a fixed node are linearly ordered. -/
theorem IsAncestor.comparable {i j k : ι} (h₁ : T.IsAncestor i j) (h₂ : T.IsAncestor i k) :
    T.IsAncestor j k ∨ T.IsAncestor k j := by
  exact Relation.ReflTransGen.total_of_right_unique
    (fun _ _ _ hab hac => Option.some_inj.1 (hab.symm.trans hac)) h₁ h₂

/-- Following parents from any bag containing `v` eventually reaches `T.top v`. -/
theorem isAncestor_top_of_mem_bag {i : ι} {v : V} (h : v ∈ T.bag i) :
    T.IsAncestor i (T.top v) := by
  generalize hn : T.rank i = n
  induction n using Nat.strong_induction_on generalizing i with
  | _ n ih =>
      by_cases hi : i = T.top v
      · subst hi; exact isAncestor_refl _
      · obtain ⟨j, hj, hvj⟩ := T.mem_bag_parent h hi
        exact Relation.ReflTransGen.head hj (ih _ (hn ▸ T.rank_parent_lt hj) hvj rfl)

/-- **Intersection property.** If `v` lies in the bag of `i`, then it lies in the bag of every node
between `i` and `T.top v`. -/
theorem mem_bag_of_isAncestor {i j : ι} {v : V} (hv : v ∈ T.bag i) (hij : T.IsAncestor i j)
    (hj : T.IsAncestor j (T.top v)) : v ∈ T.bag j := by
  revert hv
  induction hij using Relation.ReflTransGen.head_induction_on with
  | refl => exact id
  | @head a c hstep hchain ih =>
      intro hva
      by_cases ha : a = T.top v
      · have hja : T.IsAncestor j a := by rw [ha]; exact hj
        have haj : T.IsAncestor a j := Relation.ReflTransGen.head hstep hchain
        have hEq : a = j := haj.antisymm hja
        exact hEq ▸ hva
      · obtain ⟨m, hm, hvm⟩ := T.mem_bag_parent hva ha
        have hmc : m = c := Option.some_inj.1 (hm.symm.trans hstep)
        exact ih (hmc ▸ hvm)

end CliqueTree
end SimpleGraph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A **perfect elimination order** of `G`, given by an injective ranking `ord : V → ℕ`: the
neighbours of a vertex that come later in the order form a clique. -/
structure IsPEO (G : SimpleGraph V) (ord : V → ℕ) : Prop where
  /-- The ranking is injective, i.e. it is a linear order on the vertices. -/
  injective : Function.Injective ord
  /-- The later neighbourhood of every vertex is a clique. -/
  isClique_later : ∀ v : V, G.IsClique {u | ord v < ord u ∧ G.Adj v u}

/-! ### Existence of a perfect elimination order -/

/-- Every nonempty finite vertex set in a chordal graph contains a vertex whose neighbours
within that set form a clique. -/
theorem IsChordal.exists_simplicial_in_finset (hG : G.IsChordal) (S : Finset V)
    (hSne : S.Nonempty) :
    ∃ z ∈ S, ∀ a ∈ S, ∀ b ∈ S, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b := by
  classical
  obtain ⟨w, hw⟩ := hSne
  let _ : Nonempty ((S : Set V)) := ⟨⟨w, by simpa using hw⟩⟩
  obtain ⟨z, hz⟩ := (hG.induce (S : Set V)).exists_isSimplicial
  refine ⟨z, by simp, ?_⟩
  intro a ha b hb hva hvb hab
  have ha' : (⟨a, by simpa using ha⟩ : (S : Set V)) ∈
      (G.induce (S : Set V)).neighborSet z := hva
  have hb' : (⟨b, by simpa using hb⟩ : (S : Set V)) ∈
      (G.induce (S : Set V)).neighborSet z := hvb
  exact hz ha' hb' (by simp [Subtype.ext_iff, hab])

/-- Relative simplicial elimination produces an injective ranking on every finite set. -/
theorem exists_rank_of_simplicial_elimination
    (helim : ∀ (S : Finset V), S.Nonempty → ∃ z ∈ S,
      ∀ a ∈ S, ∀ b ∈ S, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → ∃ f : V → ℕ, Set.InjOn f S ∧
      ∀ v ∈ S, G.IsClique {u | u ∈ S ∧ f v < f u ∧ G.Adj v u} := by
  classical
  intro n
  induction n with
  | zero =>
      intro S hS
      rw [Finset.card_eq_zero] at hS
      subst hS
      exact ⟨fun _ => 0, by simp, by simp⟩
  | succ n ih =>
      intro S hS
      have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨z, hvS, hsimp⟩ := helim S hSne
      obtain ⟨f', hinj', hcl'⟩ := ih (S.erase (z : V))
        (by rw [Finset.card_erase_of_mem hvS, hS]; omega)
      refine ⟨fun u => if u = (z : V) then 0 else f' u + 1, ?_, ?_⟩
      · intro a ha b hb hab
        simp only at hab
        by_cases hav : a = (z : V)
        · by_cases hbv : b = (z : V)
          · rw [hav, hbv]
          · rw [ite_eq_left hav, ite_eq_right hbv] at hab
            exact absurd hab.symm (Nat.succ_ne_zero _)
        · by_cases hbv : b = (z : V)
          · rw [ite_eq_right hav, ite_eq_left hbv] at hab
            exact absurd hab (Nat.succ_ne_zero _)
          · rw [ite_eq_right hav, ite_eq_right hbv] at hab
            exact hinj' (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hav, Finset.mem_coe.1 ha⟩))
              (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hbv, Finset.mem_coe.1 hb⟩)) (by omega)
      · intro u hu
        by_cases huv : u = (z : V)
        · subst huv
          intro a ha b hb hab
          exact hsimp a ha.1 b hb.1 ha.2.2 hb.2.2 hab
        · have hmem : u ∈ S.erase (z : V) := Finset.mem_erase.2 ⟨huv, hu⟩
          refine (hcl' u hmem).subset ?_
          intro x hx
          obtain ⟨hxS, hlt, hadj⟩ := hx
          simp only [huv, ite_false] at hlt
          have hxv : x ≠ (z : V) := by
            rintro rfl
            simp at hlt
          refine ⟨Finset.mem_erase.2 ⟨hxv, hxS⟩, ?_, hadj⟩
          simp only [hxv, ite_false] at hlt
          omega

/-- Relative simpliciality in every nonempty finite vertex set yields an elimination order. -/
theorem exists_isPEO_of_simplicial_in_finset [Finite V]
    (hsimp : ∀ (S : Finset V), S.Nonempty →
      ∃ z ∈ S, ∀ a ∈ S, ∀ b ∈ S, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b) :
    ∃ ord : V → ℕ, G.IsPEO ord := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  obtain ⟨f, hinj, hclique⟩ := exists_rank_of_simplicial_elimination
    hsimp (Finset.univ.card) Finset.univ rfl
  refine ⟨f, ⟨fun a b hab => hinj (Finset.mem_coe.2 (Finset.mem_univ a))
      (Finset.mem_coe.2 (Finset.mem_univ b)) hab, fun v => ?_⟩⟩
  have := hclique v (Finset.mem_univ v)
  refine this.subset ?_
  intro u hu
  exact ⟨Finset.mem_univ u, hu.1, hu.2⟩

/-- **Every finite chordal graph has a perfect elimination order.** -/
theorem IsChordal.exists_isPEO [Finite V] (hG : G.IsChordal) :
    ∃ ord : V → ℕ, G.IsPEO ord :=
  exists_isPEO_of_simplicial_in_finset hG.exists_simplicial_in_finset

/-! ### The clique-bag decomposition of a perfect elimination order -/

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The neighbours of `v` occurring later than `v` in the order `ord`. -/
def laterNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (ord : V → ℕ) (v : V) : Finset V :=
  Finset.univ.filter fun u => ord v < ord u ∧ G.Adj v u

/-- The **clique bag** of `v`: the vertex together with its later neighbours. -/
def peoBag (G : SimpleGraph V) [DecidableRel G.Adj] (ord : V → ℕ) (v : V) : Finset V :=
  insert v (laterNbrs G ord v)

/-- The parent of `v`: its earliest later neighbour, if any. -/
noncomputable def peoParent (G : SimpleGraph V) [DecidableRel G.Adj] (ord : V → ℕ) (v : V) :
    Option V :=
  if h : (laterNbrs G ord v).Nonempty then
    some (Finset.exists_min_image (laterNbrs G ord v) ord h).choose
  else none

/-- The rank of `v`: the number of vertices occurring after `v`. -/
def peoRank (ord : V → ℕ) (v : V) : ℕ := (Finset.univ.filter fun u => ord v < ord u).card

omit [DecidableEq V] in
@[simp] theorem mem_laterNbrs {ord : V → ℕ} {v u : V} :
    u ∈ laterNbrs G ord v ↔ ord v < ord u ∧ G.Adj v u := by
  simp [laterNbrs]

@[simp] theorem mem_peoBag {ord : V → ℕ} {v u : V} :
    u ∈ peoBag G ord v ↔ u = v ∨ (ord v < ord u ∧ G.Adj v u) := by
  simp [peoBag]

theorem self_mem_peoBag {ord : V → ℕ} (v : V) : v ∈ peoBag G ord v := by simp

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem peoRank_lt_of_ord_lt {ord : V → ℕ} {u v : V} (h : ord u < ord v) :
    peoRank ord v < peoRank ord u := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    omega
  · intro hsub
    have : v ∈ Finset.univ.filter fun u => ord v < ord u := by
      exact hsub (by simp [h])
    simp at this

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem peoRank_injective {ord : V → ℕ} (h : Function.Injective ord) :
    Function.Injective (peoRank ord) := by
  intro u v huv
  rcases lt_trichotomy (ord u) (ord v) with hlt | heq | hgt
  · exact absurd huv (by simpa using (peoRank_lt_of_ord_lt hlt).ne')
  · exact h heq
  · exact absurd huv (by simpa using (peoRank_lt_of_ord_lt hgt).ne)

omit [DecidableEq V] in
theorem peoParent_spec {ord : V → ℕ} {v p : V} (hp : peoParent G ord v = some p) :
    p ∈ laterNbrs G ord v ∧ ∀ u ∈ laterNbrs G ord v, ord p ≤ ord u := by
  unfold peoParent at hp
  split at hp
  · rename_i hne
    obtain ⟨hmem, hmin⟩ := (Finset.exists_min_image (laterNbrs G ord v) ord hne).choose_spec
    rw [Option.some_inj] at hp
    subst hp
    exact ⟨hmem, hmin⟩
  · exact absurd hp (by simp)

omit [DecidableEq V] in
theorem peoParent_eq_some {ord : V → ℕ} {v : V} (hne : (laterNbrs G ord v).Nonempty) :
    ∃ p, peoParent G ord v = some p := by
  unfold peoParent
  rw [dif_pos hne]
  exact ⟨_, rfl⟩

namespace IsPEO

variable {ord : V → ℕ} (h : G.IsPEO ord)
include h

theorem peoBag_isClique (v : V) : G.IsClique (peoBag G ord v : Set V) := by
  have hcl : G.IsClique ((laterNbrs G ord v : Finset V) : Set V) := by
    refine (h.isClique_later v).subset ?_
    intro u hu
    simpa using hu
  have : ((peoBag G ord v : Finset V) : Set V) = insert v ((laterNbrs G ord v : Finset V) : Set V)
      := by simp [peoBag]
  rw [this]
  refine hcl.insert ?_
  intro b hb _
  have : b ∈ laterNbrs G ord v := by simpa using hb
  exact (mem_laterNbrs.1 this).2

theorem exists_peoBag_of_adj {u v : V} (hadj : G.Adj u v) :
    ∃ w, u ∈ peoBag G ord w ∧ v ∈ peoBag G ord w := by
  rcases lt_trichotomy (ord u) (ord v) with hlt | heq | hgt
  · exact ⟨u, self_mem_peoBag u, by simp [hlt, hadj]⟩
  · exact absurd (h.injective heq) hadj.ne
  · exact ⟨v, by simp [hgt, hadj.symm], self_mem_peoBag v⟩

theorem mem_peoBag_peoParent {v w : V} (hw : w ∈ peoBag G ord v) (hne : w ≠ v) :
    ∃ p, peoParent G ord v = some p ∧ w ∈ peoBag G ord p := by
  have hwlater : w ∈ laterNbrs G ord v := by
    rcases mem_peoBag.1 hw with rfl | hx
    · exact absurd rfl hne
    · exact mem_laterNbrs.2 hx
  obtain ⟨p, hp⟩ := peoParent_eq_some ⟨w, hwlater⟩
  refine ⟨p, hp, ?_⟩
  obtain ⟨hpmem, hpmin⟩ := peoParent_spec hp
  by_cases hpw : p = w
  · exact hpw ▸ self_mem_peoBag p
  · have hlt : ord p < ord w :=
      lt_of_le_of_ne (hpmin w hwlater) (fun hEq => hpw (h.injective hEq))
    have hadj : G.Adj p w := by
      refine h.isClique_later v ?_ ?_ hpw
      · exact ⟨(mem_laterNbrs.1 hpmem).1, (mem_laterNbrs.1 hpmem).2⟩
      · exact ⟨(mem_laterNbrs.1 hwlater).1, (mem_laterNbrs.1 hwlater).2⟩
    exact mem_peoBag.2 (Or.inr ⟨hlt, hadj⟩)

/-- **The clique-bag decomposition of a perfect elimination order is a clique tree.**
No maximality of the bags is required. -/
noncomputable def cliqueTree : CliqueTree G V where
  bag := peoBag G ord
  parent := peoParent G ord
  rank := peoRank ord
  top := id
  rank_injective := peoRank_injective h.injective
  rank_parent_lt := by
    intro i j hij
    exact peoRank_lt_of_ord_lt (mem_laterNbrs.1 (peoParent_spec hij).1).1
  bag_isClique := h.peoBag_isClique
  mem_bag_top := fun v => self_mem_peoBag v
  exists_bag_of_adj := h.exists_peoBag_of_adj
  mem_bag_parent := fun hv hi => mem_peoBag_peoParent h hv (Ne.symm hi)

end IsPEO
end SimpleGraph
