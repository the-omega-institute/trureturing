import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CzerwinskaFrancoMerinoCounterexample
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
open _root_.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
open _root_.D5.S3.Quantum.Matrix.CzerwinskaFrancoMerinoCounterexample
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix
open scoped MatrixOrder ComplexOrder

set_option autoImplicit false
noncomputable section

namespace FunctionalCalculus

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℂ) (fun n => Matrix (Fin n) (Fin n) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ A => cfc scalarFunction A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ},
    A.PosDef → R.readout () n A = rationalFunction A

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  rcases finite_certificate with ⟨hA, hB, _, hq, _⟩
  have ha := h hA
  have hb := h hB
  change (0 : Matrix (Fin 3) (Fin 3) ℂ) = rationalFunction lowerMatrix at ha
  change (0 : Matrix (Fin 3) (Fin 3) ℂ) = rationalFunction upperMatrix at hb
  rw [← ha, ← hb, sub_self] at hq
  norm_num [quadraticReadout] at hq

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, lowerMatrix, upperMatrix, ?_⟩
  intro h
  change cfc scalarFunction lowerMatrix = cfc scalarFunction upperMatrix at h
  rcases finite_certificate with ⟨hA, hB, _, hq, _⟩
  rw [cfc_rationalFunction hA, cfc_rationalFunction hB] at h
  rw [← h, sub_self] at hq
  norm_num [quadraticReadout] at hq

def source_registration : Registration arena (type_of% @cfc_rationalFunction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cfc_rationalFunction, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cfc_rationalFunction) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate.FunctionalCalculus.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate.FunctionalCalculus.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => cfc scalarFunction A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end FunctionalCalculus

end
end Reg.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
