import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Contextuality.EightVertexQutritBound
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Contextuality.EightVertexQutritBound
open _root_.D5.S3.Quantum.Contextuality.EightVertexQutritBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the full settlement predicate at the graph coordinate. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => SimpleGraph Vertex) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ G => @decide (Settled G) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ G => @decide (¬ Settled G) (Classical.propDecidable _))
    (fun e => nomatch e)

/-- Preserve both complete settlements, observing the Wagner graph operand. -/
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () W = true ∧ Settled G5

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (@of_decide_eq_true (¬ Settled W) (Classical.propDecidable _) h.1) result.1

theorem empty_not_settled : ¬ Settled (⊥ : SimpleGraph Vertex) := by
  intro h
  have hi : (⊥ : SimpleGraph Vertex).IsIndepSet (Finset.univ : Finset Vertex) := by
    simp [SimpleGraph.IsIndepSet, Set.Pairwise]
  have hc := hi.card_le_indepNum
  rw [h.1] at hc
  norm_num at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), W, ⊥, ?_⟩
  simp [actual, realize, result.1, empty_not_settled]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp [actual, realize, claim]
  variation := ⟨by simpa [arena, actual, realize, claim] using result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Contextuality.EightVertexQutritBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.EightVertexQutritBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.EightVertexQutritBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ G => @decide (Settled G) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.EightVertexQutritBound
    definition := some {
      owner := `D5.S3.Quantum.Contextuality.EightVertexQutritBound
      name := `D5.S3.Quantum.Contextuality.EightVertexQutritBound.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms rejected_law
#print axioms empty_not_settled
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Contextuality.EightVertexQutritBound
