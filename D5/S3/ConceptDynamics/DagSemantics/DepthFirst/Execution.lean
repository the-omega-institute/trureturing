/- GID: D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Execution
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DepthFirst/Execution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared-state traversal execution corresponds exactly to DFS forest postorder. -/

import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Search

namespace AdjListClass

variable
  {V : Type*} {Info : Type*}
  {EColl : Type*} [ToList EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]
  {G : Type*} [AdjListClass G V Info EColl StarColl]
  {BoolArray : Type*} [Inhabited BoolArray]
  [DefaultDict BoolArray V Bool fun _ ↦ false]

/-- Finite traversal with shared visitation and an output accumulator. Fresh vertices
are marked before child traversal and appended after all children return. -/
inductive Runs (g : G) :
    List V → BoolArray → List V → BoolArray → List V → Prop
  | nil (seen : BoolArray) (output : List V) :
      Runs g [] seen output seen output
  | skip {v : V} {work : List V}
      {seen : BoolArray} {acc : List V}
      {finalSeen : BoolArray} {finalOutput : List V}
      (hvisited : seen[v])
      (tail : Runs g work seen acc finalSeen finalOutput) :
      Runs g (v :: work) seen acc finalSeen finalOutput
  | fresh {v : V} {work : List V}
      {seen : BoolArray} {acc : List V}
      {childSeen : BoolArray} {childOutput : List V}
      {finalSeen : BoolArray} {finalOutput : List V}
      (hunvisited : ¬seen[v])
      (children :
        Runs g (succList g v) (seen[v ↦ true]) acc childSeen childOutput)
      (siblings :
        Runs g work childSeen (childOutput ++ [v]) finalSeen finalOutput) :
      Runs g (v :: work) seen acc finalSeen finalOutput

namespace Runs

/-- The independent execution relation has exactly the final visited state and
accumulated postorder of the terminating DFS forest construction. -/
theorem runs_iff_dfs_forest
    (g : G) (work : List V) (seen : BoolArray) (acc : List V)
    (finalSeen : BoolArray) (finalOutput : List V) :
    Runs g work seen acc finalSeen finalOutput ↔
      finalSeen = (dfsForest' g work seen).2.val ∧
        finalOutput = acc ++ (dfsForest' g work seen).1.post := by
  classical
  have construct :
      ∀ (work : List V) (seen : BoolArray) (acc : List V)
        (finalSeen : BoolArray) (finalOutput : List V),
        finalSeen = (dfsForest' g work seen).2.val ∧
          finalOutput = acc ++ (dfsForest' g work seen).1.post →
        Runs g work seen acc finalSeen finalOutput := by
    intro work seen
    induction work, seen using dfsForest'.induct g (BoolArray := BoolArray) with
    | case1 visited =>
        intro acc finalSeen finalOutput h
        rcases h with ⟨hseen, houtput⟩
        simpa [dfsForest', hseen, houtput] using (Runs.nil (g := g) visited acc)
    | case2 _ _ _ h ih =>
        intro acc finalSeen finalOutput hresult
        apply Runs.skip h
        apply ih acc finalSeen finalOutput
        simpa [dfsForest', h] using hresult
    | case3 visited v vs hv _ _ _ _ hc _ _ _ _ ih₁ ih₂ =>
        intro acc finalSeen finalOutput hresult
        rw [dfsForest', if_neg hv] at hresult
        dsimp at hresult
        let rc := dfsForest' g (succList g v) visited[v ↦ true]
        have hchild :
            Runs g (succList g v) (visited[v ↦ true]) acc
              rc.2.val (acc ++ rc.1.post) := by
          apply ih₁ acc rc.2.val (acc ++ rc.1.post)
          exact ⟨rfl, rfl⟩
        have hrc := congrArg (fun r ↦ r.2.val) hc
        cases hrc
        have hsibling :
            Runs g vs rc.2.val (acc ++ rc.1.post ++ [v])
              finalSeen finalOutput := by
          apply ih₂ (acc ++ rc.1.post ++ [v]) finalSeen finalOutput
          rcases hresult with ⟨hseen, houtput⟩
          constructor
          · simpa [rc] using hseen
          · simpa [rc, Forest.post, List.append_assoc] using houtput
        exact Runs.fresh hv hchild hsibling
  have characterize :
      ∀ (work : List V) (seen : BoolArray) (acc : List V)
        (finalSeen : BoolArray) (finalOutput : List V),
        Runs g work seen acc finalSeen finalOutput →
        finalSeen = (dfsForest' g work seen).2.val ∧
          finalOutput = acc ++ (dfsForest' g work seen).1.post := by
    intro work seen acc finalSeen finalOutput hr
    induction hr with
    | nil seen output =>
        simp [dfsForest']
    | @skip v work seen acc finalSeen finalOutput hvisited tail ih =>
        rw [dfsForest', if_pos hvisited]
        exact ih
    | @fresh v work seen acc childSeen childOutput finalSeen finalOutput
        hunvisited children siblings ihchildren ihsiblings =>
        rcases ihchildren with ⟨hchildSeen, hchildOutput⟩
        rcases ihsiblings with ⟨hsiblingSeen, hsiblingOutput⟩
        subst childSeen
        subst childOutput
        subst finalSeen
        subst finalOutput
        rw [dfsForest', if_neg hunvisited]
        simp [Forest.post, List.append_assoc]
  exact ⟨characterize work seen acc finalSeen finalOutput,
    construct work seen acc finalSeen finalOutput⟩

end Runs
end AdjListClass
