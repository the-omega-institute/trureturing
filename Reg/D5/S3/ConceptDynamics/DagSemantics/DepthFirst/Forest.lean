import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Forest
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Forest
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u

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
  realize signature (fun _ _ f => f.roots) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {α : Type u} (f : Forest α), (r.readout () α f : Set α) ⊆ f.support

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  exact law (Forest.nil : Forest (ULift.{u} Unit)) (a := ⟨()⟩) (Set.mem_univ _)

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Forest.roots_subset_support.{u}, rejected, rejected_law⟩
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
register_information_theorem Forest.roots_subset_support in arena
  readout via (realize signature.{u} (fun _ _ f => f.roots) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Forest
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1}] })
  escape continues (open)

end Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Forest
