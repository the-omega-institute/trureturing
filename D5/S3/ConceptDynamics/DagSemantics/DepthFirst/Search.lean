/- GID: D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Search
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DepthFirst/Search
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original shared visited DFS and inductive correctness proofs -/

/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.ForestInvariant
import Mathlib.Data.DFinsupp.Defs

/-!
Faithful excerpt port of `Algorithm/Graph/DFS.lean` from
astrainfinita/Algorithm at ce7dc1da842c7c5b8096a886d803acfb24d71a67.
Unused declarations are omitted; live thin proofs are inlined and imports normalized.
Apache-2.0 license: Library/ConceptDynamics/zhao2023algorithm.md.
Retire this port when equivalent declarations are available in this repository's
actual pinned Mathlib revision, replacing uses by direct imports and applications.
-/

namespace AdjListClass
variable {V : Type*} {Info : Type*}
  {EColl : Type*} [ToList EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]
  {G : Type*} [AdjListClass G V Info EColl StarColl]

attribute [local instance] WellFoundedLT.toWellFoundedRelation

/-- Vertices incident to an edge that have not yet been visited. -/
noncomputable def unvisitedSupport (g : G) {BoolArray : Type*}
    [DefaultDict.ReadOnly BoolArray V Bool fun _ ↦ false]
    (visited : BoolArray) : Finset V :=
  {v ∈ support g | ¬visited[v]}

def dfsForest' (g : G)
    {BoolArray : Type*}
    [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    Forest V × { b : BoolArray // {v : V | visited[v]} ⊆ {v : V | b[v]} } :=
  match vs with
  | [] => (.nil, ⟨visited, subset_rfl⟩)
  | v :: vs =>
    if visited[v] then
      dfsForest' g vs visited
    else
      have h : {w : V | visited[w]} ⊆ {w : V | visited[v ↦ true][w]} := by
        have visited_set_true :
            {w : V | visited[v ↦ true][w]} = insert v {w : V | visited[w]} := by
          classical
          ext w
          by_cases h : v = w
          · subst w
            simp
          · simp [h, Ne.symm h]
        simp [visited_set_true]
      let (fc, ⟨vis₁, h₁⟩) := dfsForest' g (succList g v) visited[v ↦ true]
      let (fs, ⟨vis₂, h₂⟩) := dfsForest' g vs vis₁
      (Forest.node v fc fs, ⟨vis₂, (h.trans h₁).trans h₂⟩)
termination_by (unvisitedSupport g visited, vs)
decreasing_by
  · simp [Prod.lex_iff]
  · classical
    have unvisitedSupport_set_true :
        unvisitedSupport g visited[v ↦ true] = (unvisitedSupport g visited).erase v := by
      classical
      ext w
      by_cases hw : w = v
      · subst hw
        simp [unvisitedSupport]
      · simp [unvisitedSupport, hw, Ne.symm hw]
    by_cases hvs : v ∈ support g
    · exact Prod.Lex.left _ _ (by
        classical
        rw [unvisitedSupport_set_true]
        exact Finset.erase_ssubset (Finset.mem_filter.mpr ⟨hvs, ‹¬visited[v]›⟩))
    · have unvisitedSupport_set_true_of_notMem :
          unvisitedSupport g visited[v ↦ true] = unvisitedSupport g visited := by
        classical
        rw [unvisitedSupport_set_true]
        exact Finset.erase_eq_of_notMem fun h ↦ hvs (Finset.mem_filter.mp h).1
      rw [unvisitedSupport_set_true_of_notMem]
      apply Prod.Lex.right
      have adj_iff_star {v w : V} : Adj g v w ↔ ∃ x ∈ g[v], snd g x = w :=
        ⟨fun ⟨e⟩ ↦ ⟨(e : E g).info,
          Eq.mp (congrArg (fun u : V ↦ (e : E g).info ∈ g[u])
            (show (e : E g).fst = v from congr_arg ToQuiver.val e.2.1)) (e : E g).mem_star,
          congr_arg ToQuiver.val e.2.2⟩,
          fun ⟨e, he, h⟩ ↦ h ▸ ⟨homOfStar e he⟩⟩
      have star_ne_empty {v w : V} (h : Adj g v w) : g[v] ≠ ∅ := by
        obtain ⟨e, he, -⟩ := adj_iff_star.mp h
        intro hv
        exact not_mem_empty e (hv ▸ he)
      have mem_support {v : V} : v ∈ support g ↔ ∃ w, Adj g v w ∨ Adj g w v := by
        classical
        have membership (f : DFinsupp' (fun _ : V => EColl) (fun _ => ∅)) (v : V) :
            v ∈ f.support ↔ f v ≠ ∅ := by
          let : Zero EColl := ⟨∅⟩
          let original : DFinsupp (fun _ : V => EColl) := ⟨f.toFun, f.support'⟩
          exact DFinsupp.mem_support_toFun original v
        simp only [support, Finset.mem_biUnion, membership,
          coe_toDFinsupp'_eq_getElem, Multiset.mem_toFinset, mem_toMultiset,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨u, _, e, he, rfl | rfl⟩
          · exact ⟨snd g e, .inl ⟨homOfStar e he⟩⟩
          · exact ⟨u, .inr ⟨homOfStar e he⟩⟩
        · rintro ⟨w, h | h⟩
          · obtain ⟨e, he, rfl⟩ := adj_iff_star.mp h
            exact ⟨v, star_ne_empty h, e, he, .inl rfl⟩
          · obtain ⟨e, he, rfl⟩ := adj_iff_star.mp h
            exact ⟨w, star_ne_empty h, e, he, .inr rfl⟩
      have hnil : succList g v = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro w hw
        have mem_succList_iff : w ∈ succList g v ↔ Adj g v w := by
          simp [succList, ← adj_iff_star]
        exact hvs (mem_support.mpr ⟨w, .inl (mem_succList_iff.mp hw)⟩)
      cases vs <;> simp +arith [hnil]
  · simpa [Prod.lex_iff] using
      lt_or_eq_of_le (α := Finset V)
        (show unvisitedSupport g vis₁ ⊆ unvisitedSupport g visited from
          fun v hv ↦ Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hv).1,
              mt (fun hvisited ↦ (h.trans h₁) hvisited) (Finset.mem_filter.mp hv).2⟩)

lemma roots_dfsForest'_fst_subset (g : G)
    {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    (dfsForest' g vs visited).1.roots ⊆ {v | v ∈ vs} := by
  match vs with
  | [] => unfold dfsForest'; exact Set.empty_subset _
  | v :: vs =>
    unfold dfsForest'; split
    · intro _ h
      simpa using .inr (roots_dfsForest'_fst_subset g vs visited h)
    dsimp
    rintro _ (rfl | h)
    · simp
    · simp only [List.mem_cons]
      exact .inr <| roots_dfsForest'_fst_subset g vs _ h

lemma subset_visited_dfsForest'_snd (g : G)
    {BoolArray : Type*}
    [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    {v | v ∈ vs} ⊆ {v : V | (dfsForest' g vs visited).2.val[v]} := by
  match vs with
  | [] => simp
  | v :: vs =>
    simp only [List.mem_cons]
    unfold dfsForest'; split
    · rintro _ (rfl | h)
      · apply (dfsForest' g vs visited).2.prop
        simpa
      · exact subset_visited_dfsForest'_snd g vs visited h
    · dsimp
      rintro _ (rfl | h)
      · apply (dfsForest' g _ _).2.prop
        apply (dfsForest' g _ _).2.prop
        simp
      · exact subset_visited_dfsForest'_snd g vs _ h

lemma isDFSForest_dfsForest' (g : G)
    {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    IsDFSForest g
      {v : V | visited[v]}
      {v : V | (dfsForest' g vs visited).2.val[v]}
      (dfsForest' g vs visited).1 := by
  induction vs, visited using dfsForest'.induct g (BoolArray := BoolArray) with
  | case1 => unfold dfsForest'; constructor
  | case2 _ _ _ h ih => rwa [dfsForest', if_pos h]
  | case3 visited v vs hv _ _ _ _ hc _ _ _ _ ih₁ ih₂ =>
    rw [dfsForest', if_neg hv]
    let rc := dfsForest' g (succList g v) visited[v ↦ true]
    dsimp; apply IsDFSForest.node {v : V | rc.2.val[v]}
    · simp [hv]
    · have visited_set_true :
          {w : V | visited[v ↦ true][w]} = insert v {w : V | visited[w]} := by
        classical
        ext w
        by_cases h : v = w
        · subst w
          simp
        · simp [h, Ne.symm h]
      simpa [visited_set_true] using ih₁
    · have adj_iff_star {v w : V} : Adj g v w ↔ ∃ x ∈ g[v], snd g x = w :=
        ⟨fun ⟨e⟩ ↦ ⟨(e : E g).info,
          Eq.mp (congrArg (fun u : V ↦ (e : E g).info ∈ g[u])
            (show (e : E g).fst = v from congr_arg ToQuiver.val e.2.1)) (e : E g).mem_star,
          congr_arg ToQuiver.val e.2.2⟩,
          fun ⟨e, he, h⟩ ↦ h ▸ ⟨homOfStar e he⟩⟩
      have succList_eq_succSet : {w | w ∈ succList g v} = succSet g {v} := by
        ext w
        simp [succList, succSet, adj_iff_star]
      exact succList_eq_succSet ▸ (roots_dfsForest'_fst_subset g _ _)
    · have adj_iff_star {v w : V} : Adj g v w ↔ ∃ x ∈ g[v], snd g x = w :=
        ⟨fun ⟨e⟩ ↦ ⟨(e : E g).info,
          Eq.mp (congrArg (fun u : V ↦ (e : E g).info ∈ g[u])
            (show (e : E g).fst = v from congr_arg ToQuiver.val e.2.1)) (e : E g).mem_star,
          congr_arg ToQuiver.val e.2.2⟩,
          fun ⟨e, he, h⟩ ↦ h ▸ ⟨homOfStar e he⟩⟩
      have succList_eq_succSet : {w | w ∈ succList g v} = succSet g {v} := by
        ext w
        simp [succList, succSet, adj_iff_star]
      exact succList_eq_succSet ▸ (subset_visited_dfsForest'_snd g _ _)
    · have hrc := congrArg (fun r ↦ r.2.val) hc
      cases hrc
      exact ih₂

def dfsForest (g : G)
    {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    Forest V × BoolArray :=
  (dfsForest' g vs visited).map id Subtype.val

end AdjListClass
