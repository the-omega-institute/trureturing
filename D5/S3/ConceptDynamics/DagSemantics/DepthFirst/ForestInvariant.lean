/- GID: D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original DFS forest invariant and inductive correctness proofs -/

/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Forest
import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Adjacency

/-!
Faithful excerpt port of `Algorithm/Data/Graph/IsDFSForest.lean` from
astrainfinita/Algorithm at ce7dc1da842c7c5b8096a886d803acfb24d71a67.
Unused declarations are omitted; live thin proofs are inlined and imports normalized.
Apache-2.0 license: Library/ConceptDynamics/zhao2023algorithm.md.
Retire this port when equivalent declarations are available in this repository's
actual pinned Mathlib revision, replacing uses by direct imports and applications.
-/

namespace AdjListClass
variable
  {V : Type*} {Info : Type*}
  {EColl : Type*} [ToList EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]
  {G : Type*} [AdjListClass G V Info EColl StarColl] {g : G}

variable (g) in
inductive IsDFSForest : Set V → Set V → Forest V → Prop
  | nil (i : Set V) : IsDFSForest i i .nil
  | node {i o : Set V} {v : V} {c : Forest V} {s : Forest V}
    (m : Set V)
    (hv : v ∉ i)
    (hc : IsDFSForest (insert v i) m c)
    (roots_subset_succ : c.roots ⊆ succSet g {v})
    (succ_marked : succSet g {v} ⊆ m)
    (hs : IsDFSForest m o s) : IsDFSForest i o (.node v c s)

namespace IsDFSForest
variable {i m o : Set V} {f f₁ f₂ : Forest V}

lemma union (hf : IsDFSForest g i o f) : i ∪ f.support = o := by
  induction hf with
  | nil i => exact Set.union_empty _
  | node _ _ _ _ _ _ ihc ihs =>
    dsimp
    rw [Set.union_insert, ← Set.insert_union,
      ← Set.union_assoc, ihc, ihs]

lemma inter (hf : IsDFSForest g i o f) : i ∩ f.support = ∅ := by
  induction hf with
  | nil _ => exact Set.inter_empty _
  | node _ hv hc _ _ _ ihc ihs =>
    dsimp
    rw [Set.inter_insert_of_notMem hv, Set.inter_union_distrib_left,
      Set.union_empty_iff]
    rw [← Set.subset_empty_iff] at ihc ihs ⊢
    rw [← Set.subset_empty_iff]
    exact ⟨(Set.inter_subset_inter_left _ (Set.subset_insert _ _)).trans ihc,
      (Set.inter_subset_inter_left _ ((Set.subset_insert _ _).trans (hc.union ▸ Set.subset_union_left))).trans ihs⟩

lemma sound (hf : IsDFSForest g i o f) :
    ∀ v ∈ f.support, ∃ r ∈ f.roots, Reachable g r v := by
  induction hf with
  | nil _ => nofun
  | node _ hv hc roots_subset_succ _ _ ihc ihs =>
    dsimp
    rintro w (rfl | hw | hw)
    · exact ⟨w, .inl rfl, ⟨.nil⟩⟩
    · obtain ⟨r, hr, hrw⟩ := ihc w hw
      exact ⟨_, .inl rfl,
        Nonempty.map2 .comp
          ((show Adj g _ r from by simpa [succSet] using roots_subset_succ hr).map
            (·.toPath)) hrw⟩
    · obtain ⟨r, hr, hrw⟩ := ihs w hw
      exact ⟨r, .inr hr, hrw⟩

lemma succSet_support_subset (hf : IsDFSForest g i o f) :
    succSet g f.support ⊆ o := by
  induction hf with
  | nil _ => nofun
  | node _ hv hc _ succ_marked hs ihc ihs =>
    dsimp
    intro w hw
    simp only [Set.mem_union, succSet, Set.mem_ofPred_eq, Set.mem_insert_iff, exists_eq_or_imp] at hw
    obtain (hw | ⟨r, (hr | hr), hrw⟩) := hw
    · apply succ_marked.trans (hs.union ▸ Set.subset_union_left)
      simpa [succSet] using hw
    · apply ihc.trans (hs.union ▸ Set.subset_union_left)
      simpa [succSet] using ⟨r, hr, hrw⟩
    · apply ihs
      simpa [succSet] using ⟨r, hr, hrw⟩


end IsDFSForest

end AdjListClass
