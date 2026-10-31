import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
import Reg.Support.SingleDependentReadout

/-! The scalar readout varies its actual real parameter while retaining the
full absolute-convergence and signed-operator statement. -/

noncomputable section
open scoped BigOperators Topology
open Filter
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ r => ((r / (4 * (1 - r)) : ℝ) : ℂ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    Summable (fun n : ℕ => ‖weightedSource r hr.le hr1 n *
      oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n‖) ∧
    (∑' n : ℕ, weightedSource r hr.le hr1 n *
      oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n) =
        R.readout () () r

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have ha := (bilinear_opposite_resolvent_scalar (r := 1 / 2) (by norm_num)
    (by norm_num)).2
  have hb := (h (r := 1 / 2) (by norm_num) (by norm_num)).2
  rw [ha] at hb
  norm_num [rejected, realize] at hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  norm_num [actual, realize]
  exact Complex.ofReal_injective.ne (by norm_num : (0 : ℝ) ≠ 1 / 4)

def evidence : Registration arena (type_of% @bilinear_opposite_resolvent_scalar) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bilinear_opposite_resolvent_scalar, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bilinear_opposite_resolvent_scalar) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.scalarUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.evidence
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
    (fun _ _ r => ((r / (4 * (1 - r)) : ℝ) : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private theorem F_zero : F 0 = 1 := by
  have hp : _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod.period 0 = 1 := by
    calc
      _ = (_root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.halfBinomial 0) ^ 2 *
          (0 : ℂ) ^ 0 :=
        tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])
      _ = 1 := by simp [_root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.halfBinomial]
  simp [F, hp]

private theorem source_half_ne_zero :
    weightedSource (1 / 2) (by norm_num) (by norm_num) ≠ 0 := by
  intro hz
  have h := (bilinear_opposite_resolvent_scalar (r := 1 / 2) (by norm_num)
    (by norm_num)).2
  norm_num [hz] at h

private theorem column_half_ne_zero :
    weightedColumn (1 / 2) (by norm_num) (by norm_num) ≠ 0 := by
  intro hz
  have he := opposite_resolvent_weighted_source (r := 1 / 2) (by norm_num) (by norm_num)
  rw [hz, smul_zero] at he
  have h := (bilinear_opposite_resolvent_scalar (r := 1 / 2) (by norm_num)
    (by norm_num)).2
  rw [he] at h
  norm_num at h

namespace Column

def actual : Realization signature :=
  realize signature (fun _ _ r => 1 / ((Real.sqrt (1 - r) : ℂ) * (F r : ℂ)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ r => 1 / ((Real.sqrt (1 - r) : ℂ) * (F r : ℂ)) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    (1 + operator (Real.sqrt r : ℂ)) (weightedColumn r hr.le hr1) =
      R.readout () () r • weightedSource r hr.le hr1

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have ha := weightedColumn_equation (r := 1 / 2) (by norm_num) (by norm_num)
  have hb := h (r := 1 / 2) (by norm_num) (by norm_num)
  have he := ha.symm.trans hb
  change _ • weightedSource (1 / 2) _ _ =
    (_ + (1 : ℂ)) • weightedSource (1 / 2) _ _ at he
  have hh := smul_left_injective ℂ source_half_ne_zero he
  have hn : (0 : ℂ) = 1 := by linear_combination hh
  exact zero_ne_one hn

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, F_zero]

def evidence : Registration arena (type_of% @weightedColumn_equation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weightedColumn_equation, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weightedColumn_equation) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.Column.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.Column.evidence
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
    (fun _ _ r => 1 / ((Real.sqrt (1 - r) : ℂ) * (F r : ℂ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Column

namespace Opposite

def actual : Realization signature :=
  realize signature (fun _ _ r => ((Real.sqrt (1 - r) * F r : ℝ) : ℂ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ r => ((Real.sqrt (1 - r) * F r : ℝ) : ℂ) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) =
      R.readout () () r • weightedColumn r hr.le hr1

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have ha := opposite_resolvent_weighted_source (r := 1 / 2) (by norm_num) (by norm_num)
  have hb := h (r := 1 / 2) (by norm_num) (by norm_num)
  have he := ha.symm.trans hb
  change _ • weightedColumn (1 / 2) _ _ =
    (_ + (1 : ℂ)) • weightedColumn (1 / 2) _ _ at he
  have hh := smul_left_injective ℂ column_half_ne_zero he
  have hn : (0 : ℂ) = 1 := by linear_combination hh
  exact zero_ne_one hn

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, F_zero]

def evidence : Registration arena (type_of% @opposite_resolvent_weighted_source) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@opposite_resolvent_weighted_source, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@opposite_resolvent_weighted_source) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.Opposite.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.Opposite.evidence
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
    (fun _ _ r => ((Real.sqrt (1 - r) * F r : ℝ) : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Opposite


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
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.FiniteDeterminant.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.FiniteDeterminant.evidence
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
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
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.DeterminantLimit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.DeterminantLimit.evidence
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
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

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
