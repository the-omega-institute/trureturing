import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
import Reg.Support.SingleDependentReadout

/-! The actual determinant readouts retain every natural cutoff and complex
argument in the open unit disk. -/

noncomputable section
open scoped BigOperators Topology
open Filter
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant

private lemma determinant_zero (N : ℕ) : Matrix.det (1 - finiteSection N 0 ^ 2) = 1 := by
  have hA : finiteSection N 0 = 0 := by
    ext i j
    simp [finiteSection, matrixEntry, zero_pow (by omega : (i.val + 1) + (j.val + 1) ≠ 0)]
  simp [hA]

private lemma determinant_one_half :
    Matrix.det (1 - finiteSection 1 (1 / 2) ^ 2) = (1023 / 1024 : ℂ) := by
  norm_num [Matrix.det_fin_one, pow_two, Matrix.sub_apply, Matrix.mul_apply,
    finiteSection, matrixEntry, pairScalar, halfBinomial]

namespace FiniteDeterminant

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ N z => Complex.exp (finiteLog N z)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) (z : ℂ), ‖z‖ < 1 →
    Matrix.det (1 - finiteSection N z ^ 2) = R.readout () N z

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 (by norm_num)
  simpa [rejected, realize, determinant_zero] using hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1 / 2, ?_⟩
  change Complex.exp (finiteLog 1 0) ≠ Complex.exp (finiteLog 1 (1 / 2))
  rw [← finite_determinant_identity 1 0 (by norm_num), determinant_zero,
    ← finite_determinant_identity 1 (1 / 2) (by norm_num), determinant_one_half]
  norm_num

def evidence : Registration arena (type_of% @finite_determinant_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_determinant_identity, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_determinant_identity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.FiniteDeterminant.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.FiniteDeterminant.evidence
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
    (fun _ N z => Complex.exp (finiteLog N z)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteDeterminant

namespace DeterminantLimit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℕ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z N => Matrix.det (1 - finiteSection N z ^ 2))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {z : ℂ}, ‖z‖ < 1 →
    Tendsto (R.readout () () z) atTop (𝓝 (gaussianDet z))

private theorem gaussianDet_zero : gaussianDet 0 = 1 := by
  have ht := finite_determinants_tendsto (z := 0) (by norm_num)
  simp only [determinant_zero] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have ht := h (z := 0) (by norm_num)
  have he : (0 : ℂ) = gaussianDet 0 := tendsto_nhds_unique tendsto_const_nhds ht
  simpa [gaussianDet_zero] using he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  intro h
  have he := congrFun h 1
  change Matrix.det (1 - finiteSection 1 0 ^ 2) =
    Matrix.det (1 - finiteSection 1 (1 / 2) ^ 2) at he
  rw [determinant_zero, determinant_one_half] at he
  norm_num at he

def evidence : Registration arena (type_of% @finite_determinants_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_determinants_tendsto, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_determinants_tendsto) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.DeterminantLimit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.DeterminantLimit.evidence
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
    (fun _ _ z N => Matrix.det (1 - finiteSection N z ^ 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeterminantLimit

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
