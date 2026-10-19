import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.BasisMeasurementProjection
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Measurement.BasisMeasurementProjection
open _root_.D5.S3.Quantum.Measurement.BasisMeasurementProjection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.checkUnivs false
noncomputable section

open _root_.D5.S3.Observer.Conditioning
open _root_.D5.S3.Quantum.Tomography.RankOneContextCommutator
open _root_.D5.S3.Quantum.Measurement.BasisMeasurementProjection

private def oneContext : RankOneContext 1 where
  projector := fun _ => 1
  rankOne := by
    intro j
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro X
    ext i k
    fin_cases i
    fin_cases k
    simp [Matrix.trace, Matrix.mul_apply]
  resolvesIdentity := by simp

private theorem oneContext_record : IsRecordMeasurement oneContext.projector := by
  refine ⟨?_, ?_, ?_, oneContext.resolvesIdentity⟩
  · intro j
    simp [oneContext]
  · intro j
    simp [oneContext]
  · intro j k hjk
    exact (hjk (Subsingleton.elim _ _)).elim

namespace Expansion

abbrev signature : Signature where
  Params := ℕ
  State p := Matrix (Fin p) (Fin p) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (B : RankOneContext d) (A : HermitianSpace d),
    basisMeasurement B A =
      ∑ j, (R.readout () d (B.projector j * A.1)).re • basisProjector B j

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : HermitianSpace 1 => A.1 0 0) (h oneContext 0)
  norm_num [rejected, realize, basisMeasurement_val, basisProjector_val, oneContext] at he

def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Measurement.BasisMeasurementProjection.basis_measurement_eq_projector_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.Law actual from (@_root_.D5.S3.Quantum.Measurement.BasisMeasurementProjection.basis_measurement_eq_projector_sum), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    simp [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.BasisMeasurementProjection.basis_measurement_eq_projector_sum) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.BasisMeasurementProjection.Expansion.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.BasisMeasurementProjection.Expansion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.BasisMeasurementProjection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Expansion

end
end Reg.D5.S3.Quantum.Measurement.BasisMeasurementProjection
