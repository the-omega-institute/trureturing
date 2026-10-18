import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
open _root_.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix
open scoped MatrixOrder ComplexOrder

set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 3) (Fin 3) ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ X => quadraticReadout X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := lowerMatrix.PosDef ∧ upperMatrix.PosDef ∧ lowerMatrix ≤ upperMatrix ∧
    R.readout () () (rationalFunction upperMatrix - rationalFunction lowerMatrix) =
      -(2 / 111549375 : ℝ) ∧
    0 < ((rationalFunction upperMatrix - rationalFunction lowerMatrix) 0 0).re

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.2.2.2.1
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : Matrix (Fin 3) (Fin 3) ℂ),
    (1 : Matrix (Fin 3) (Fin 3) ℂ), ?_⟩
  norm_num [actual, realize, quadraticReadout, testVector, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, Matrix.one_apply, Matrix.zero_apply, Pi.zero_apply, map_ofNat, map_neg]

def source_registration : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@finite_certificate) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate.source_registration
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
    (fun _ _ X => quadraticReadout X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

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

namespace Monotonicity
open _root_.D5.S3.Quantum.Matrix.RadialConvexity
open Classical

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ f => decide (MatrixMonotoneDegree 3 f)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ R.readout () () scalarFunction = true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h rfl

private theorem zero_monotone : MatrixMonotoneDegree 3 (fun _ => 0) := by
  left
  intro A B _ _ _
  simp only [matFun, cfc_const_zero]
  exact le_refl _

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), scalarFunction, (fun _ => 0), by
    simp [actual, realize, not_matrix_monotone, zero_monotone]⟩

def source_registration : Registration arena (type_of% @not_matrix_monotone) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using not_matrix_monotone,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@not_matrix_monotone) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate.Monotonicity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate.Monotonicity.source_registration
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
    (fun _ _ f => decide (MatrixMonotoneDegree 3 f)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Monotonicity

end
end Reg.D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
