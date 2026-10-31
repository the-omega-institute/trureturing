import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierGraph
import Reg.Support.DependentFamily

/-! Source-bound audit of the outgoing-multiplicity recurrence. -/

namespace Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierGraph

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Maths Maths.EdgeGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the appended edge's source, which decides the outgoing increment. -/
abbrev signature.{u, v} : Signature where
  Params := Σ V : Type u, Σ E : Type v, EdgeGraph V E
  State q := q.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := q.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u, v} : Realization signature.{u, v} :=
  realize signature (fun _ q edge => q.2.2.source edge) (fun e => nomatch e)

def rejected.{u, v} : Realization signature.{u, v} :=
  realize signature (fun _ q edge => q.2.2.target edge) (fun e => nomatch e)

abbrev arena.{u, v} : Arena where
  signature := signature.{u, v}
  Law R := ∀ {V : Type u} {E : Type v} {G : EdgeGraph V E} {start finish : V}
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (vertex : V),
    G.outgoingMultiplicity (Walk.concat walkSoFar edge legal).edgeMultiplicity vertex =
      G.outgoingMultiplicity walkSoFar.edgeMultiplicity vertex +
        if R.readout () ⟨V, E, G⟩ edge = vertex then 1 else 0

private def oneEdge.{u, v} : EdgeGraph (ULift.{u} Bool) PUnit.{v + 1} where
  source _ := ⟨false⟩
  target _ := ⟨true⟩

theorem rejected_law.{u, v} : ¬ arena.{u, v}.Law rejected := by
  intro h
  have hb := h (G := oneEdge) .nil ⟨⟩ rfl ⟨false⟩
  have hne : (⟨true⟩ : ULift.{u} Bool) ≠ ⟨false⟩ :=
    fun he => Bool.noConfusion (congrArg ULift.down he)
  norm_num [rejected, realize, oneEdge, outgoingMultiplicity, Walk.edgeMultiplicity, hne] at hb

theorem dependence.{u, v} : ObservationalDependence signature.{u, v} actual := by
  intro i
  let G : EdgeGraph (ULift.{u} Bool) (ULift.{v} Bool) := {
    source := fun e => ⟨e.down⟩
    target := fun e => ⟨e.down⟩ }
  refine ⟨⟨ULift.{u} Bool, ULift.{v} Bool, G⟩, ⟨false⟩, ⟨true⟩, ?_⟩
  exact fun h => Bool.noConfusion (congrArg ULift.down h)

def source_registration.{u, v} : Registration arena.{u, v}
    (type_of% @Walk.outgoingMultiplicity_edgeMultiplicity_concat.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Walk.outgoingMultiplicity_edgeMultiplicity_concat, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u, v} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@Walk.outgoingMultiplicity_edgeMultiplicity_concat.{u, v})
      (Realization signature.{u, v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierGraph.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierGraph.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q edge => q.2.2.source edge) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierGraph
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "fn", "fn", "fn", "arg", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print Maths.EdgeGraph.Walk.outgoingMultiplicity_edgeMultiplicity_concat
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierGraph
