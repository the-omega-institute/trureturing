import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Execution
import Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Models

namespace Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Execution

open AdjListClass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w z t q

def signature : Signature where
  Params := Type u
  State V := List V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := List V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ output => output) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

/-- Preserve the whole execution equivalence; observe the final output in its equation. -/
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} {Info : Type v}
    {EColl : Type w} [ToList EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    {StarColl : Type z} [DefaultDict.ReadOnly StarColl V EColl fun _ => ∅]
    {G : Type t} [AdjListClass G V Info EColl StarColl]
    {BoolArray : Type q} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ => false]
    (g : G) (work : List V) (seen : BoolArray) (acc : List V)
    (finalSeen : BoolArray) (finalOutput : List V),
    Runs g work seen acc finalSeen finalOutput ↔
      finalSeen = (dfsForest' g work seen).2.val ∧
        r.readout () V finalOutput = acc ++ (dfsForest' g work seen).1.post

theorem rejected_law : ¬ arena.{u,v,w,z,t,q}.Law rejected := by
  intro law
  let seen : ULift.{q} Bool := ⟨false⟩
  let acc : List Models.V.{u} := [⟨()⟩]
  have h := (law Models.empty.{u,v,w,z,t} [] seen acc seen acc).mp
    (Runs.nil seen acc)
  have bad := h.2
  simpa [rejected, realize, dfsForest', Forest.post, acc] using bad

def registration : Registration arena.{u,v,w,z,t,q} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Runs.runs_iff_dfs_forest.{u,v,w,z,t,q}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j different
      exact (different (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro role
    refine ⟨ULift.{u} Unit, [], [⟨()⟩], ?_⟩
    change ([] : List (ULift.{u} Unit)) ≠ [⟨()⟩]
    simp

register_information_theorem Runs.runs_iff_dfs_forest in arena
  readout via (realize signature.{u} (fun _ _ output => output) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Execution
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 18 }] })
  escape continues (open)

end Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Execution
