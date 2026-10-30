import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation
import Reg.Support.SingleDependentReadout

/-! Source-bound registration for the projector resolution identity. -/

namespace Reg.D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation

open _root_.D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation
open _root_.D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation
  (measurementProjector)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Σ d : ℕ, Matrix.unitaryGroup (Fin d) ℂ
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1) (Fin p.1) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (a : Matrix.unitaryGroup (Fin d) ℂ),
    R.readout () ⟨d, a⟩ (∑ i, measurementProjector a i) 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (d := 0) (1 : Matrix.unitaryGroup (Fin 0) ℂ)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, (0 : Matrix (Fin 1) (Fin 1) ℂ), 1, ?_⟩
  intro he
  have hbad : (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact zero_ne_one hbad.symm

def source_registration : Registration arena
    (type_of% @sum_projectors) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_projectors, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sum_projectors) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
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
end Reg.D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation
