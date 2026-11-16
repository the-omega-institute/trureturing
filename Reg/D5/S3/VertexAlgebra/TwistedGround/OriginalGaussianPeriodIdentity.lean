import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ r => 1 - r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ {r : ℝ}, 0 ≤ r → r < 1 →
    gaussianDet (Real.sqrt r : ℂ) =
      ((Real.rpow (A.readout () () r) (1 / 4 : ℝ) * F r : ℝ) : ℂ)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 0) le_rfl (by norm_num)
  norm_num [rejected, realize, gaussianDet_zero, Real.rpow_eq_pow, Real.zero_rpow] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  norm_num [actual, realize]

def evidence : Registration arena (type_of% @gaussianDet_real_period_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gaussianDet_real_period_identity, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussianDet_real_period_identity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => 1 - r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace SectionZero

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ℕ (fun _ => ℂ) (fun N => Matrix (Fin N) (Fin N) ℂ)

def actual : Realization signature :=
  realize signature (fun _ N z => finiteSection N z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ N : ℕ, A.readout () N 0 = 0

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) (h 1)
  change (1 : ℂ) = 0 at hh
  norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1 / 2, ?_⟩
  intro he
  have hh := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) he
  norm_num [actual, realize, finiteSection, matrixEntry, pairScalar, halfBinomial] at hh

def evidence : Registration arena (type_of% @finiteSection_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finiteSection_zero, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finiteSection_zero) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.SectionZero.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.SectionZero.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N z => finiteSection N z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SectionZero

namespace FiniteLogZero

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ N z => finiteLog N z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ N : ℕ, A.readout () N 0 = 0

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  norm_num [rejected, realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1 / 2, ?_⟩
  change finiteLog 1 0 ≠ finiteLog 1 (1 / 2)
  rw [finiteLog_zero]
  intro he
  have hd := finite_determinant_identity 1 (1 / 2) (by norm_num)
  rw [← he, Complex.exp_zero] at hd
  norm_num [Matrix.det_fin_one, pow_two, Matrix.mul_apply, finiteSection,
    matrixEntry, pairScalar, halfBinomial] at hd

def evidence : Registration arena (type_of% @finiteLog_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finiteLog_zero, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finiteLog_zero) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.FiniteLogZero.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.FiniteLogZero.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N z => finiteLog N z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteLogZero

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
