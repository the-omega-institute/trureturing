import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.CommutingMidpoint
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the Bloch commutator Gram identity. -/

namespace Reg.D5.S3.Quantum.CommutingMidpoint.BlochCommutatorGram

open _root_.D5.S3.Quantum.CommutingMidpoint (bloch_commutator_gram)
open _root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum (blochMatrix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the equality relation between the two real Gram expressions. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Both Bloch vectors and the complete source equality remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ a b : EuclideanSpace ℝ (Fin 3),
    let P := blochMatrix 1 a
    let Q := blochMatrix 1 b
    r.readout () () (trace ((P * Q - Q * P)ᴴ * (P * Q - Q * P))).re
      ((‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2) / 2)

private theorem rejected_law : ¬ arena.Law rejected := fun h => h 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def source_registration : Registration arena (type_of% @bloch_commutator_gram) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bloch_commutator_gram, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bloch_commutator_gram) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.CommutingMidpoint.bloch_commutator_gram.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.CommutingMidpoint.BlochCommutatorGram.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.CommutingMidpoint
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.CommutingMidpoint.BlochCommutatorGram
