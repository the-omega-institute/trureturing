import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Search
import Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Models

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Search
open AdjListClass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v w z t q

abbrev signature : Signature where
  Params := Type u
  State V := List V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := List V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ vs => vs) (fun e => nomatch e)

namespace Roots
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} {Info : Type v}
    {EColl : Type w} [ToList EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    {StarColl : Type z} [DefaultDict.ReadOnly StarColl V EColl fun _ => ∅]
    {G : Type t} [AdjListClass G V Info EColl StarColl] (g : G)
    {BoolArray : Type q} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ => false]
    (vs : List V) (visited : BoolArray),
    (dfsForest' g vs visited).1.roots ⊆ {a | a ∈ (r.readout () V vs : List V)}

theorem rejected_law : ¬ arena.{u,v,w,z,t,q}.Law rejected := by
  intro law
  have h := law Models.empty.{u,v,w,z,t} [⟨()⟩] (⟨false⟩ : ULift.{q} Bool)
  have ha : (⟨()⟩ : Models.V.{u}) ∈
      (dfsForest' Models.empty.{u,v,w,z,t} [⟨()⟩] (⟨false⟩ : ULift.{q} Bool)).1.roots := by
    simp [dfsForest', succList, Models.empty]
  exact List.not_mem_nil (h ha)

def registration : Registration arena.{u,v,w,z,t,q} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@roots_dfsForest'_fst_subset.{u,v,w,z,t,q}, rejected, rejected_law⟩
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
register_information_theorem roots_dfsForest'_fst_subset in arena
  readout via (realize signature.{u} (fun _ _ vs => vs) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Search
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 14 }] })
  escape continues (open)

end Roots

namespace Visited
def rejected : Realization signature.{u} := by
  classical
  exact realize signature (fun _ V _ => if h : Nonempty V then [Classical.choice h] else [])
    (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} {Info : Type v}
    {EColl : Type w} [ToList EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    {StarColl : Type z} [DefaultDict.ReadOnly StarColl V EColl fun _ => ∅]
    {G : Type t} [AdjListClass G V Info EColl StarColl] (g : G)
    {BoolArray : Type q} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ => false]
    (vs : List V) (visited : BoolArray),
    {a | a ∈ (r.readout () V vs : List V)} ⊆
      {a : V | (dfsForest' g vs visited).2.val[a]}

theorem rejected_law : ¬ arena.{u,v,w,z,t,q}.Law rejected := by
  classical
  intro law
  have h := law Models.empty.{u,v,w,z,t} [] (⟨false⟩ : ULift.{q} Bool)
  have ha : (⟨()⟩ : Models.V.{u}) ∈ rejected.readout () Models.V.{u} [] := by
    simp [rejected, realize, Subsingleton.elim (Classical.choice (inferInstance : Nonempty Models.V.{u})) (⟨()⟩ : Models.V.{u})]
    exact ⟨()⟩
  have bad := h ha
  simp [dfsForest', Models.visited] at bad

def registration : Registration arena.{u,v,w,z,t,q} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@subset_visited_dfsForest'_snd.{u,v,w,z,t,q}, rejected, rejected_law⟩
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
register_information_theorem subset_visited_dfsForest'_snd in arena
  readout via (realize signature.{u} (fun _ _ vs => vs) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Search
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 14 }] })
  escape continues (open)

end Visited

namespace Invariant
abbrev signature : Signature where
  Params := Type q
  State B := B
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ B := B
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{q} :=
  realize signature (fun _ _ b => b) (fun e => nomatch e)
def rejected : Realization signature.{q} := by
  classical
  exact realize signature
    (fun _ => Function.update (fun (B : Type q) (b : B) => b)
      (ULift.{q} Bool) (fun _ => ⟨true⟩)) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{q}
  Law r := ∀ {V : Type u} {Info : Type v}
    {EColl : Type w} [ToList EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    {StarColl : Type z} [DefaultDict.ReadOnly StarColl V EColl fun _ => ∅]
    {G : Type t} [AdjListClass G V Info EColl StarColl] (g : G)
    {BoolArray : Type q} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ => false]
    (vs : List V) (visited : BoolArray),
    IsDFSForest g {a : V | (r.readout () BoolArray visited : BoolArray)[a]}
      {a : V | (dfsForest' g vs visited).2.val[a]}
      (dfsForest' g vs visited).1

theorem rejected_law : ¬ arena.{u,v,w,z,t,q}.Law rejected := by
  classical
  intro law
  have hf := law Models.empty.{u,v,w,z,t} [] (⟨false⟩ : ULift.{q} Bool)
  have eq := hf.union
  have point := congrArg (fun s : Set Models.V.{u} => (⟨()⟩ : Models.V.{u}) ∈ s) eq
  simp [rejected, realize, dfsForest'] at point

def registration : Registration arena.{u,v,w,z,t,q} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isDFSForest_dfsForest'.{u,v,w,z,t,q}, rejected, rejected_law⟩
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
    refine ⟨ULift.{q} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
    intro same
    cases same
register_information_theorem isDFSForest_dfsForest' in arena
  readout via (realize signature.{q} (fun _ _ b => b) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Search
    coordinates := #[11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg", "arg", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 15 }] })
  escape continues (open)

end Invariant

end Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Search
