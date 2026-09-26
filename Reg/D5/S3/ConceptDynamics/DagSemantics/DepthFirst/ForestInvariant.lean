import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.ForestInvariant
import Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Models

namespace Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.ForestInvariant
open AdjListClass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v w z t

abbrev signature : Signature where
  Params := Type u
  State V := Forest V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := Set V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => f.support) (fun e => nomatch e)

namespace Union
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} {Info : Type v}
    {EColl : Type w} [ToList EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    {StarColl : Type z} [DefaultDict.ReadOnly StarColl V EColl fun _ => ∅]
    {G : Type t} [AdjListClass G V Info EColl StarColl] {g : G}
    {i o : Set V} {f : Forest V} (_hf : IsDFSForest g i o f), i ∪ (r.readout () V f : Set V) = o

theorem rejected_law : ¬ arena.{u,v,w,z,t}.Law rejected := by
  intro law
  have eq := law Models.singleton_dfs.{u,v,w,z,t}
  have point := congrArg (fun s : Set Models.V.{u} => (⟨()⟩ : Models.V.{u}) ∈ s) eq
  simp [rejected, realize] at point

def registration : Registration arena.{u,v,w,z,t} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsDFSForest.union.{u,v,w,z,t}, rejected, rejected_law⟩
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
    refine ⟨ULift.{u} Unit, .nil, .node ⟨()⟩ .nil .nil, ?_⟩
    intro same
    have atVertex := congrArg (fun s : Set (ULift.{u} Unit) => (⟨()⟩ : ULift.{u} Unit) ∈ s) same
    simp [actual, realize] at atVertex
register_information_theorem IsDFSForest.union in arena
  readout via (realize signature.{u} (fun _ _ f => f.support) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DagSemantics.DepthFirst.ForestInvariant
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 13}] })
  escape continues (open)

end Union

namespace Inter
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} {Info : Type v}
    {EColl : Type w} [ToList EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    {StarColl : Type z} [DefaultDict.ReadOnly StarColl V EColl fun _ => ∅]
    {G : Type t} [AdjListClass G V Info EColl StarColl] {g : G}
    {i o : Set V} {f : Forest V} (_hf : IsDFSForest g i o f), i ∩ (r.readout () V f : Set V) = ∅

theorem rejected_law : ¬ arena.{u,v,w,z,t}.Law rejected := by
  intro law
  have eq := law (IsDFSForest.nil (g := Models.empty.{u,v,w,z,t}) Set.univ)
  have point := congrArg (fun s : Set Models.V.{u} => (⟨()⟩ : Models.V.{u}) ∈ s) eq
  simp [rejected, realize] at point

def registration : Registration arena.{u,v,w,z,t} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsDFSForest.inter.{u,v,w,z,t}, rejected, rejected_law⟩
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
    refine ⟨ULift.{u} Unit, .nil, .node ⟨()⟩ .nil .nil, ?_⟩
    intro same
    have atVertex := congrArg (fun s : Set (ULift.{u} Unit) => (⟨()⟩ : ULift.{u} Unit) ∈ s) same
    simp [actual, realize] at atVertex
register_information_theorem IsDFSForest.inter in arena
  readout via (realize signature.{u} (fun _ _ f => f.support) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DagSemantics.DepthFirst.ForestInvariant
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 13}] })
  escape continues (open)

end Inter

namespace Sound
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} {Info : Type v}
    {EColl : Type w} [ToList EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    {StarColl : Type z} [DefaultDict.ReadOnly StarColl V EColl fun _ => ∅]
    {G : Type t} [AdjListClass G V Info EColl StarColl] {g : G}
    {i o : Set V} {f : Forest V} (_hf : IsDFSForest g i o f), ∀ a ∈ (r.readout () V f : Set V), ∃ b ∈ f.roots, Reachable g b a

theorem rejected_law : ¬ arena.{u,v,w,z,t}.Law rejected := by
  intro law
  obtain ⟨b, hb, _⟩ := law (IsDFSForest.nil (g := Models.empty.{u,v,w,z,t}) ∅) ⟨()⟩ (Set.mem_univ _)
  exact hb

def registration : Registration arena.{u,v,w,z,t} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsDFSForest.sound.{u,v,w,z,t}, rejected, rejected_law⟩
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
    refine ⟨ULift.{u} Unit, .nil, .node ⟨()⟩ .nil .nil, ?_⟩
    intro same
    have atVertex := congrArg (fun s : Set (ULift.{u} Unit) => (⟨()⟩ : ULift.{u} Unit) ∈ s) same
    simp [actual, realize] at atVertex
register_information_theorem IsDFSForest.sound in arena
  readout via (realize signature.{u} (fun _ _ f => f.support) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DagSemantics.DepthFirst.ForestInvariant
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 13}] })
  escape continues (open)

end Sound

namespace Successors
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} {Info : Type v}
    {EColl : Type w} [ToList EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    {StarColl : Type z} [DefaultDict.ReadOnly StarColl V EColl fun _ => ∅]
    {G : Type t} [AdjListClass G V Info EColl StarColl] {g : G}
    {i o : Set V} {f : Forest V} (_hf : IsDFSForest g i o f), succSet g ((r.readout () V f : Set V)) ⊆ o

theorem rejected_law : ¬ arena.{u,v,w,z,t}.Law rejected := by
  intro law
  exact law (IsDFSForest.nil (g := Models.loop.{u,v,w,z,t}) ∅)
    ⟨⟨()⟩, Set.mem_univ _, Models.loop_adj⟩

def registration : Registration arena.{u,v,w,z,t} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsDFSForest.succSet_support_subset.{u,v,w,z,t}, rejected, rejected_law⟩
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
    refine ⟨ULift.{u} Unit, .nil, .node ⟨()⟩ .nil .nil, ?_⟩
    intro same
    have atVertex := congrArg (fun s : Set (ULift.{u} Unit) => (⟨()⟩ : ULift.{u} Unit) ∈ s) same
    simp [actual, realize] at atVertex
register_information_theorem IsDFSForest.succSet_support_subset in arena
  readout via (realize signature.{u} (fun _ _ f => f.support) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DagSemantics.DepthFirst.ForestInvariant
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 13}] })
  escape continues (open)

end Successors


end Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.ForestInvariant
