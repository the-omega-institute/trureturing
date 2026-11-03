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
abbrev signature.{uV, uE} : Signature where
  Params := Σ V : Type uV, Σ E : Type uE, EdgeGraph V E
  State q := q.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := q.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{uV, uE} : Realization signature.{uV, uE} :=
  realize signature (fun _ q edge => q.2.2.source edge) (fun e => nomatch e)

def rejected.{uV, uE} : Realization signature.{uV, uE} :=
  realize signature (fun _ q edge => q.2.2.target edge) (fun e => nomatch e)

abbrev arena.{uV, uE} : Arena where
  signature := signature.{uV, uE}
  Law R := ∀ {V : Type uV} {E : Type uE} {G : EdgeGraph V E} {start finish : V}
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (vertex : V),
    G.outgoingMultiplicity (Walk.concat walkSoFar edge legal).edgeMultiplicity vertex =
      G.outgoingMultiplicity walkSoFar.edgeMultiplicity vertex +
        if R.readout () ⟨V, E, G⟩ edge = vertex then 1 else 0

private def oneEdge.{uV, uE} : EdgeGraph (ULift.{uV} Bool) PUnit.{uE + 1} where
  source _ := ⟨false⟩
  target _ := ⟨true⟩

theorem rejected_law.{uV, uE} : ¬ arena.{uV, uE}.Law rejected := by
  intro h
  have hb := h (G := oneEdge) .nil ⟨⟩ rfl ⟨false⟩
  have hne : (⟨true⟩ : ULift.{uV} Bool) ≠ ⟨false⟩ :=
    fun he => Bool.noConfusion (congrArg ULift.down he)
  norm_num [rejected, realize, oneEdge, outgoingMultiplicity, Walk.edgeMultiplicity, hne] at hb

theorem dependence.{uV, uE} : ObservationalDependence signature.{uV, uE} actual := by
  intro i
  let G : EdgeGraph (ULift.{uV} Bool) (ULift.{uE} Bool) := {
    source := fun e => ⟨e.down⟩
    target := fun e => ⟨e.down⟩ }
  refine ⟨⟨ULift.{uV} Bool, ULift.{uE} Bool, G⟩, ⟨false⟩, ⟨true⟩, ?_⟩
  exact fun h => Bool.noConfusion (congrArg ULift.down h)

def source_registration.{uV, uE} : Registration arena.{uV, uE}
    (type_of% @Walk.outgoingMultiplicity_edgeMultiplicity_concat.{uV, uE}) where
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

def registration.{uV, uE} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@Walk.outgoingMultiplicity_edgeMultiplicity_concat.{uV, uE})
      (Realization signature.{uV, uE}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierGraph.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierGraph.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uV, uE}⟩
  objectArena := .source ⟨arena.{uV, uE}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{uV, uE} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{uV, uE}
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
        "body", "body", "body", "body", "arg", "arg", "fn", "fn", "fn", "arg",
        "fn", "arg"]
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
