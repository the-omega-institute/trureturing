import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.Polarization
import Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.Chirp

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
open LeanInformationAudit
open Matrix
open scoped Matrix

namespace Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D

set_option autoImplicit false

noncomputable section

private abbrev SpatialMatrix := Matrix (Fin 3) (Fin 3) ℝ

private def auditAxis : Fin 3 → ℝ := ![0, 0, 1]

private theorem auditAxis_unit : IsUnitVec3 auditAxis := by
  norm_num [IsUnitVec3, auditAxis, Fin.sum_univ_three]

private theorem ttProj_zero (n : Fin 3 → ℝ) : ttProj n 0 = 0 := by simp [ttProj]

private theorem ttProj_axis_plus : ttProj auditAxis ePlus = ePlus := by
  have hP : transverseProj auditAxis = !![1, 0, 0; 0, 1, 0; 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [transverseProj, auditAxis]
  rw [ttProj, hP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, ePlus,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

private theorem plus_nonzero : ePlus ≠ 0 := by
  intro he
  have h := congrArg (fun A : SpatialMatrix => A 0 0) he
  norm_num [ePlus] at h

abbrev projectorSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 3 → ℝ)
    (fun _ => SpatialMatrix) (fun _ => SpatialMatrix)

def projectorActual : Realization projectorSignature :=
  realize projectorSignature (fun _ n h => ttProj n h) (fun e => nomatch e)

def projectorConstant (A : SpatialMatrix) : Realization projectorSignature :=
  realize projectorSignature (fun _ _ _ => A) (fun e => nomatch e)

private theorem projector_dependence :
    ∀ i : projectorSignature.Role, ∃ (p : projectorSignature.Params)
      (x y : projectorSignature.State p), projectorActual.readout i p x ≠
        projectorActual.readout i p y := by
  intro _
  refine ⟨auditAxis, ePlus, 0, ?_⟩
  change ttProj auditAxis ePlus ≠ ttProj auditAxis 0
  simpa [ttProj_axis_plus, ttProj_zero] using plus_nonzero

abbrev symmetricArena : Arena where
  signature := projectorSignature
  Law R := ∀ (n : Fin 3 → ℝ) (h : SpatialMatrix), hᵀ = h → (R.readout () n h)ᵀ = ttProj n h

private theorem symmetric_counterexample : ¬ symmetricArena.Law (projectorConstant ePlus) := by
  intro hlaw
  have he : ePlusᵀ = ttProj auditAxis 0 := hlaw auditAxis 0 (by simp)
  rw [ttProj_zero] at he
  exact plus_nonzero (by simpa using congrArg Matrix.transpose he)

def symmetricFamily : Registration symmetricArena (type_of% (@ttProj_symmetric)) where
  actual := projectorActual
  bridge := Iff.rfl
  variation := ⟨ttProj_symmetric, projectorConstant ePlus, symmetric_counterexample⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    symmetricArena.Law projectorActual (projectorConstant ePlus) symmetric_counterexample
  dependence := projector_dependence

def symmetricRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ttProj_symmetric) (Realization projectorSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.ttProj_symmetric.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.symmetricFamily
  realizationSource := none
  generated := false
  arena := .source ⟨symmetricArena⟩
  objectArena := .source ⟨symmetricArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source symmetricArena ⟨symmetricFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectorSignature
    (fun _ n h => ttProj n h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev transverseArena : Arena where
  signature := projectorSignature
  Law R := ∀ (n : Fin 3 → ℝ), IsUnitVec3 n →
    ∀ h : SpatialMatrix, (R.readout () n h).mulVec n = 0

private theorem transverse_counterexample : ¬ transverseArena.Law (projectorConstant 1) := by
  intro hlaw
  have he : (1 : SpatialMatrix).mulVec auditAxis = 0 := hlaw auditAxis auditAxis_unit 0
  rw [Matrix.one_mulVec] at he
  have hf := congrFun he (2 : Fin 3)
  norm_num [auditAxis] at hf

def transverseFamily : Registration transverseArena (type_of% (@ttProj_transverse)) where
  actual := projectorActual
  bridge := Iff.rfl
  variation := ⟨ttProj_transverse, projectorConstant 1, transverse_counterexample⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    transverseArena.Law projectorActual (projectorConstant 1) transverse_counterexample
  dependence := projector_dependence

def transverseRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ttProj_transverse) (Realization projectorSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.ttProj_transverse.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.transverseFamily
  realizationSource := none
  generated := false
  arena := .source ⟨transverseArena⟩
  objectArena := .source ⟨transverseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transverseArena ⟨transverseFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectorSignature
    (fun _ n h => ttProj n h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev tracelessArena : Arena where
  signature := projectorSignature
  Law R := ∀ (n : Fin 3 → ℝ), IsUnitVec3 n →
    ∀ h : SpatialMatrix, Matrix.trace (R.readout () n h) = 0

private theorem traceless_counterexample : ¬ tracelessArena.Law (projectorConstant 1) := by
  intro hlaw
  have he : Matrix.trace (1 : SpatialMatrix) = 0 := hlaw auditAxis auditAxis_unit 0
  norm_num [Matrix.trace_one] at he

def tracelessFamily : Registration tracelessArena (type_of% (@ttProj_traceless)) where
  actual := projectorActual
  bridge := Iff.rfl
  variation := ⟨ttProj_traceless, projectorConstant 1, traceless_counterexample⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    tracelessArena.Law projectorActual (projectorConstant 1) traceless_counterexample
  dependence := projector_dependence

def tracelessRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ttProj_traceless) (Realization projectorSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.ttProj_traceless.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.tracelessFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tracelessArena⟩
  objectArena := .source ⟨tracelessArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tracelessArena ⟨tracelessFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectorSignature
    (fun _ n h => ttProj n h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev idempotentArena : Arena where
  signature := projectorSignature
  Law R := ∀ (n : Fin 3 → ℝ), IsUnitVec3 n →
    ∀ h : SpatialMatrix, ttProj n (R.readout () n h) = ttProj n h

private theorem idempotent_counterexample : ¬ idempotentArena.Law (projectorConstant 0) := by
  intro hlaw
  have he : ttProj auditAxis 0 = ttProj auditAxis ePlus := hlaw auditAxis auditAxis_unit ePlus
  rw [ttProj_zero, ttProj_axis_plus] at he
  exact plus_nonzero he.symm

def idempotentFamily : Registration idempotentArena (type_of% (@ttProj_idempotent)) where
  actual := projectorActual
  bridge := Iff.rfl
  variation := ⟨ttProj_idempotent, projectorConstant 0, idempotent_counterexample⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    idempotentArena.Law projectorActual (projectorConstant 0) idempotent_counterexample
  dependence := projector_dependence

def idempotentRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ttProj_idempotent) (Realization projectorSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.ttProj_idempotent.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.idempotentFamily
  realizationSource := none
  generated := false
  arena := .source ⟨idempotentArena⟩
  objectArena := .source ⟨idempotentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source idempotentArena ⟨idempotentFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectorSignature
    (fun _ n h => ttProj n h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev adjointArena : Arena where
  signature := projectorSignature
  Law R := ∀ (n : Fin 3 → ℝ) (h k : SpatialMatrix),
    Matrix.trace ((R.readout () n h)ᵀ * k) = Matrix.trace (hᵀ * ttProj n k)

private theorem adjoint_counterexample : ¬ adjointArena.Law (projectorConstant 0) := by
  intro hlaw
  have he : Matrix.trace ((0 : SpatialMatrix)ᵀ * ePlus) =
      Matrix.trace (ePlusᵀ * ttProj auditAxis ePlus) := hlaw auditAxis ePlus ePlus
  rw [ttProj_axis_plus] at he
  norm_num [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, ePlus] at he

def adjointFamily : Registration adjointArena (type_of% (@ttProj_selfAdjoint)) where
  actual := projectorActual
  bridge := Iff.rfl
  variation := ⟨ttProj_selfAdjoint, projectorConstant 0, adjoint_counterexample⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    adjointArena.Law projectorActual (projectorConstant 0) adjoint_counterexample
  dependence := projector_dependence

def adjointRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ttProj_selfAdjoint) (Realization projectorSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.ttProj_selfAdjoint.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.adjointFamily
  realizationSource := none
  generated := false
  arena := .source ⟨adjointArena⟩
  objectArena := .source ⟨adjointArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source adjointArena ⟨adjointFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectorSignature
    (fun _ n h => ttProj n h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev transverseSpecSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3 → ℝ) (fun _ => SpatialMatrix)

def transverseSpecActual : Realization transverseSpecSignature :=
  realize transverseSpecSignature (fun _ _ n => transverseProj n) (fun e => nomatch e)

def transverseSpecErased : Realization transverseSpecSignature :=
  realize transverseSpecSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev transverseSpecArena : Arena where
  signature := transverseSpecSignature
  Law R := ∀ n : Fin 3 → ℝ, IsUnitVec3 n →
    (transverseProj n)ᵀ = transverseProj n ∧
    transverseProj n * transverseProj n = transverseProj n ∧
    (transverseProj n).mulVec n = 0 ∧ Matrix.trace (R.readout () () n) = 2

private theorem transverseSpec_erased_fails : ¬ transverseSpecArena.Law transverseSpecErased := by
  intro hlaw
  have h : Matrix.trace (0 : SpatialMatrix) = 2 := (hlaw auditAxis auditAxis_unit).2.2.2
  norm_num at h

def transverseSpecFamily : Registration transverseSpecArena (type_of% (@transverseProj_spec)) where
  actual := transverseSpecActual
  bridge := Iff.rfl
  variation := ⟨transverseProj_spec, transverseSpecErased, transverseSpec_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    transverseSpecArena.Law transverseSpecActual transverseSpecErased transverseSpec_erased_fails
  dependence := by
    intro _
    refine ⟨(), auditAxis, ![1, 0, 0], ?_⟩
    intro he
    have h := congrArg (fun A : SpatialMatrix => A 0 0) he
    change transverseProj auditAxis 0 0 = transverseProj ![1, 0, 0] 0 0 at h
    norm_num [transverseProj, auditAxis] at h

def transverseSpecRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@transverseProj_spec) (Realization transverseSpecSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.transverseProj_spec.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.transverseSpecFamily
  realizationSource := none
  generated := false
  arena := .source ⟨transverseSpecArena⟩
  objectArena := .source ⟨transverseSpecArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transverseSpecArena ⟨transverseSpecFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize transverseSpecSignature
    (fun _ _ n => transverseProj n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
