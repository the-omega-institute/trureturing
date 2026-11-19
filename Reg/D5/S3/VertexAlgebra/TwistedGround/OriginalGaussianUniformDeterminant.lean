import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant
import Reg.Support.SingleDependentReadout

/-! Typed whole-family readouts for the original uniform logarithm and determinant limits. -/

noncomputable section
open scoped Topology
open Filter
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℂ) (fun _ => ℂ)

private theorem det_one_half :
    Matrix.det (1 - finiteSection 1 (1 / 2 : ℂ) ^ 2) = 1023 / 1024 := by
  norm_num [Matrix.det_fin_one, pow_two, Matrix.mul_apply, finiteSection,
    matrixEntry, pairScalar, halfBinomial]

namespace Log

def actual : Realization signature :=
  realize signature (fun _ N z => finiteLog N z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ {ρ : ℝ}, 0 ≤ ρ → ρ < 1 →
    TendstoUniformlyOn (fun N z => A.readout () N z) gaussianLogDet
      atTop {z : ℂ | ‖z‖ ≤ ρ}

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have ht := (h (ρ := 0) le_rfl (by norm_num)).tendsto_at (x := 0) (by simp)
  have he := tendsto_nhds_unique ht tendsto_const_nhds
  have hre := congrArg Complex.re he
  norm_num [gaussianLogDet_zero, rejected, realize] at hre

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1 / 2, ?_⟩
  change finiteLog 1 0 ≠ finiteLog 1 (1 / 2)
  rw [finiteLog_zero]
  intro he
  have hd := finite_determinant_identity 1 (1 / 2) (by norm_num)
  rw [← he, Complex.exp_zero, det_one_half] at hd
  norm_num at hd

def evidence : Registration arena (type_of% @finiteLog_tendstoUniformlyOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finiteLog_tendstoUniformlyOn, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finiteLog_tendstoUniformlyOn) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant.Log.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant.Log.evidence
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Log

namespace Det

def actual : Realization signature :=
  realize signature (fun _ N z => Matrix.det (1 - finiteSection N z ^ 2))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ {ρ : ℝ}, 0 ≤ ρ → ρ < 1 →
    TendstoUniformlyOn (fun N z => A.readout () N z)
      (fun z => Complex.exp ((1 / 4 : ℂ) * Complex.log (1 - z ^ 2)) *
        _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod.period (z ^ 2))
      atTop {z : ℂ | ‖z‖ ≤ ρ}

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have ht := (h (ρ := 0) le_rfl (by norm_num)).tendsto_at (x := 0) (by simp)
  have he := tendsto_nhds_unique ht tendsto_const_nhds
  have hp := gaussianDet_complex_period_identity (z := 0) (by norm_num)
  rw [← hp, gaussianDet_zero] at he
  have hre := congrArg Complex.re he
  norm_num [rejected, realize] at hre

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1 / 2, ?_⟩
  change Matrix.det (1 - finiteSection 1 0 ^ 2) ≠
    Matrix.det (1 - finiteSection 1 (1 / 2 : ℂ) ^ 2)
  rw [finiteSection_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero,
    Matrix.det_one, det_one_half]
  norm_num

def evidence : Registration arena (type_of% @finite_determinants_tendstoUniformlyOn_period) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_determinants_tendstoUniformlyOn_period, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_determinants_tendstoUniformlyOn_period) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant.Det.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant.Det.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ N z => Matrix.det (1 - finiteSection N z ^ 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Det
end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant
