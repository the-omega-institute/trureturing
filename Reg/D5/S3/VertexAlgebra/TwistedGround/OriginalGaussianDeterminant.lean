import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
import Reg.Support.SingleDependentReadout

/-! The actual determinant readouts retain every natural cutoff and complex
argument in the open unit disk. -/

noncomputable section
open scoped BigOperators Topology
open Filter
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
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


namespace EntryBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ × ℕ × ℕ) (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ q z => unit1Entry z q.2.1 q.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ {ρ : ℝ}, 0 ≤ ρ → ∀ {z : ℂ}, ‖z‖ ≤ ρ → ∀ i j : ℕ,
    ‖A.readout () (ρ, i, j) z‖ ≤ unit1Geo ρ (i, j)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h (ρ := 0) le_rfl (z := 0) (by simp) 0 0
  norm_num [rejected, realize, unit1Geo] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0, 0, 0), 0, 1 / 2, ?_⟩
  change unit1Entry 0 0 0 ≠ unit1Entry (1 / 2) 0 0
  norm_num [unit1Entry, matrixEntry, pairScalar, halfBinomial]

def evidence : Registration arena (type_of% @unit1Entry_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@unit1Entry_bound, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unit1Entry_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.EntryBound.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.EntryBound.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q z => unit1Entry z q.2.1 q.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
    definition := none
    coordinates := #[0, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EntryBound

namespace ContractNBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℝ × ℕ × ℕ × (ℕ × ℕ)) (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ q z => unit1ContractN q.2.1 z q.2.2.1 q.2.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ {ρ : ℝ}, 0 ≤ ρ → ρ < 1 → ∀ {z : ℂ}, ‖z‖ ≤ ρ →
    ∀ (N p : ℕ) (a : ℕ × ℕ),
    ‖A.readout () (ρ, N, p, a) z‖ ≤ unit1Geo ρ a * (ρ ^ 2) ^ p

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h (ρ := 0) le_rfl (by norm_num) (z := 0) (by simp) 1 0 (0, 0)
  norm_num [rejected, realize, unit1Geo] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0, 1, 0, (0, 0)), 0, 1 / 2, ?_⟩
  change unit1ContractN 1 0 0 (0, 0) ≠ unit1ContractN 1 (1 / 2) 0 (0, 0)
  norm_num [unit1ContractN, unit1EntryN, unit1Entry, basis, lp.single_apply,
    matrixEntry, pairScalar, halfBinomial]

def evidence : Registration arena (type_of% @unit1ContractN_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@unit1ContractN_bound, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unit1ContractN_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.ContractNBound.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.ContractNBound.evidence
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
    (fun _ q z => unit1ContractN q.2.1 z q.2.2.1 q.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
    definition := none
    coordinates := #[0, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ContractNBound

namespace ContractNTrace

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) (fun _ => ℂ) (fun _ => (ℕ × ℕ) → ℂ)

def actual : Realization signature :=
  realize signature (fun _ q z a => unit1ContractN q.1 z q.2 a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ (N : ℕ) (z : ℂ) (p : ℕ),
    (∑' a : ℕ × ℕ, A.readout () (N, p) z a) =
      Matrix.trace (finiteSection N z ^ (p + 1))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (1 / 2) 0
  norm_num [rejected, realize, Matrix.trace, finiteSection, matrixEntry,
    pairScalar, halfBinomial] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(1, 0), 0, 1 / 2, ?_⟩
  intro he
  have hh := congrFun he (0, 0)
  change unit1ContractN 1 0 0 (0, 0) = unit1ContractN 1 (1 / 2) 0 (0, 0) at hh
  norm_num [unit1ContractN, unit1EntryN, unit1Entry, basis, lp.single_apply,
    matrixEntry, pairScalar, halfBinomial] at hh

def evidence : Registration arena (type_of% @unit1ContractN_tsum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@unit1ContractN_tsum, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unit1ContractN_tsum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.ContractNTrace.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.ContractNTrace.evidence
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
    (fun _ q z a => unit1ContractN q.1 z q.2 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ContractNTrace

abbrev diffSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ)
    (fun _ => Set ℂ → Prop)
def diffActual : Realization diffSignature :=
  realize _ (fun _ _ f s => DifferentiableOn ℂ f s) (fun e => nomatch e)
def diffBad : Realization diffSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem diffDependence : ObservationalDependence diffSignature diffActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun z => z⁻¹), ?_⟩
  intro h
  have he := congrFun h Set.univ
  have hd : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) Set.univ :=
    Eq.mp he (differentiableOn_const _)
  have hi := differentiableOn_univ.mp hd (0 : ℂ)
  exact (differentiableAt_inv_iff.mp hi) rfl


namespace finiteLog_diff
def arena : Arena where
  signature := diffSignature
  Law A := ∀ N : ℕ, A.readout () () (finiteLog N) (Metric.ball (0 : ℂ) 1)
private theorem bad_fails : ¬ arena.Law diffBad := by
  intro h
  exact h 0
def evidence : Registration arena (type_of% (@finiteLog_diff)) where
  actual := diffActual
  bridge := Iff.rfl
  variation := ⟨@finiteLog_diff, diffBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law diffActual diffBad bad_fails
  dependence := diffDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finiteLog_diff) (Realization diffSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.finiteLog_diff.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant.finiteLog_diff.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diffSignature diffActual.readout diffActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end finiteLog_diff

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
