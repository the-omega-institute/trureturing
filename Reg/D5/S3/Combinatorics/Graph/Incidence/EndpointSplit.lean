import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Incidence.EndpointSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Incidence.EndpointSplit

open _root_.D5.S3.Combinatorics.Graph.Incidence.EndpointSplit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph

noncomputable section

universe u

abbrev signature : Signature where
  Params := Type u
  State V := Set (Sym2 V)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => Nat.card s) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

open scoped Sym2

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let x : Sym2 (ULift.{u} Unit) := s(⟨()⟩, ⟨()⟩)
  refine ⟨ULift.{u} Unit, {x}, ∅, ?_⟩
  change Nat.card ({x} : Set (Sym2 (ULift.{u} Unit))) ≠ Nat.card (∅ : Set (Sym2 (ULift.{u} Unit)))
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_singleton, Set.ncard_empty]
  decide

/-- The complete edge-bijection count with the root edge count as readout. -/
abbrev edgeArena : Arena where
  signature := signature.{u}
  Law O := ∀ {V : Type u} {F : SimpleGraph V} (P : EndpointPartition F),
    Nat.card P.splitGraph.edgeSet = O.readout () V F.edgeSet

/-- The complete incidence count with the root edge count as readout. -/
abbrev incidenceArena : Arena where
  signature := signature.{u}
  Law O := ∀ {V : Type u} {F : SimpleGraph V} (P : EndpointPartition F) [Finite V],
    Nat.card (Σ b : P.Block, P.Members b) = 2 * O.readout () V F.edgeSet

private def emptyPartition : EndpointPartition (⊥ : SimpleGraph (ULift.{u} Unit)) :=
  fun _ => ⊤

private theorem edgeFamilyRejected : ¬ edgeArena.{u}.Law rejected := by
  intro h
  have hz : Nat.card (⊥ : SimpleGraph (ULift.{u} Unit)).edgeSet = 0 := by
    rw [edgeSet_bot, Nat.card_coe_set_eq, Set.ncard_empty]
  have hbad := h emptyPartition
  change Nat.card emptyPartition.splitGraph.edgeSet = 1 at hbad
  rw [emptyPartition.card_edgeSet, hz] at hbad
  contradiction

private theorem incidenceFamilyRejected : ¬ incidenceArena.{u}.Law rejected := by
  intro h
  have hz : Nat.card (⊥ : SimpleGraph (ULift.{u} Unit)).edgeSet = 0 := by
    rw [edgeSet_bot, Nat.card_coe_set_eq, Set.ncard_empty]
  have hbad := h emptyPartition
  change Nat.card (Σ b : emptyPartition.Block, emptyPartition.Members b) = 2 * 1 at hbad
  rw [card_total_members emptyPartition, hz] at hbad
  contradiction

def edgeFamily : Registration edgeArena.{u} (type_of% @EndpointPartition.card_edgeSet.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@EndpointPartition.card_edgeSet.{u}, rejected, edgeFamilyRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, edgeFamilyRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def edgeFamilyRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@EndpointPartition.card_edgeSet.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Incidence.EndpointSplit.EndpointPartition.card_edgeSet.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.EndpointSplit.edgeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨edgeArena⟩
  objectArena := .source ⟨edgeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source edgeArena ⟨edgeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => Nat.card s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.EndpointSplit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms edgeFamilyRegistration

def incidenceFamily : Registration incidenceArena.{u} (type_of% @card_total_members.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@card_total_members.{u}, rejected, incidenceFamilyRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, incidenceFamilyRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def incidenceFamilyRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@card_total_members.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Incidence.EndpointSplit.card_total_members.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.EndpointSplit.incidenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨incidenceArena⟩
  objectArena := .source ⟨incidenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source incidenceArena ⟨incidenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => Nat.card s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.EndpointSplit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms incidenceFamilyRegistration

end
end Reg.D5.S3.Combinatorics.Graph.Incidence.EndpointSplit
