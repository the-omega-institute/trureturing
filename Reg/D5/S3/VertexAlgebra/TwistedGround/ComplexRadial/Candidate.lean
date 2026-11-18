import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianComplexRadialContinuation OriginalGaussianExternalGeneratedSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate

abbrev realSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def realLess : Realization realSignature :=
  realize _ (fun _ _ x y => x < y) (fun e => nomatch e)
def realLe : Realization realSignature :=
  realize _ (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def realBad : Realization realSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem realLessDependence : ObservationalDependence realSignature realLess := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℝ) < 1 := Eq.mp (congrFun h 1) (by norm_num : (0 : ℝ) < 1)
  exact lt_irrefl 1 hh
private theorem realLeDependence : ObservationalDependence realSignature realLe := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) (by norm_num : (0 : ℝ) ≤ 0)
  norm_num at hh
abbrev analyticSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℂ → ℂ) (fun _ => Set ℂ → Prop)
def analyticActual : Realization analyticSignature :=
  realize _ (fun _ _ f s => AnalyticOnNhd ℂ f s) (fun e => nomatch e)
def analyticBad : Realization analyticSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem analyticDependence : ObservationalDependence analyticSignature analyticActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun z => z⁻¹), ?_⟩
  intro h
  have hc : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ :=
    fun _ _ => analyticAt_const
  have hi : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) Set.univ := Eq.mp (congrFun h Set.univ) hc
  have hd : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) 0 := (hi 0 (Set.mem_univ _)).differentiableAt
  exact (differentiableAt_inv_iff.mp hd) rfl

namespace norm_lt_sourceRadius_iff
abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ (u v z : ℂ), R.readout () () ‖z‖ (sourceRadius u v) ↔
    (‖u‖ + ‖z‖ < 1 ∧ ‖v‖ + ‖z‖ < 1)
private theorem rejected_fails : ¬ arena.Law realBad := by
  intro hh
  exact (hh 0 0 0).mpr (by norm_num)
def family : Registration arena (type_of% (@norm_lt_sourceRadius_iff)) where
  actual := realLess
  bridge := Iff.rfl
  variation := ⟨@norm_lt_sourceRadius_iff, realBad, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law realLess realBad rejected_fails
  dependence := realLessDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@norm_lt_sourceRadius_iff) (Realization realSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate.norm_lt_sourceRadius_iff.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate.norm_lt_sourceRadius_iff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature realLess.readout realLess.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end norm_lt_sourceRadius_iff

namespace sourceRadius_pos
abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ {u v : ℂ} (_hu : ‖u‖ < 1) (_hv : ‖v‖ < 1),
    R.readout () () 0 (sourceRadius u v)
private theorem rejected_fails : ¬ arena.Law realBad := by
  intro hh
  exact hh (u := 0) (v := 0) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@sourceRadius_pos)) where
  actual := realLess
  bridge := Iff.rfl
  variation := ⟨@sourceRadius_pos, realBad, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law realLess realBad rejected_fails
  dependence := realLessDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceRadius_pos) (Realization realSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate.sourceRadius_pos.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate.sourceRadius_pos.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature realLess.readout realLess.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceRadius_pos

namespace sourceRadius_le_one
abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ (u v : ℂ), R.readout () () (sourceRadius u v) 1
private theorem rejected_fails : ¬ arena.Law realBad := by
  intro hh
  exact hh 0 0
def family : Registration arena (type_of% (@sourceRadius_le_one)) where
  actual := realLe
  bridge := Iff.rfl
  variation := ⟨@sourceRadius_le_one, realBad, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law realLe realBad rejected_fails
  dependence := realLeDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceRadius_le_one) (Realization realSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate.sourceRadius_le_one.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate.sourceRadius_le_one.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature realLe.readout realLe.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceRadius_le_one

namespace candidate_square_analyticOnNhd
abbrev arena : Arena where
  signature := analyticSignature
  Law R := ∀ (square e f : Bool) (u v : ℂ),
    R.readout () () (fun z => signedCandidate square e f u v (z ^ 2))
      (Metric.ball 0 (sourceRadius u v))
private theorem rejected_fails : ¬ arena.Law analyticBad := by
  intro hh
  exact hh false false false 0 0
def family : Registration arena (type_of% (@candidate_square_analyticOnNhd)) where
  actual := analyticActual
  bridge := Iff.rfl
  variation := ⟨@candidate_square_analyticOnNhd, analyticBad, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law analyticActual analyticBad rejected_fails
  dependence := analyticDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidate_square_analyticOnNhd) (Realization analyticSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate.candidate_square_analyticOnNhd.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate.candidate_square_analyticOnNhd.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize analyticSignature analyticActual.readout analyticActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end candidate_square_analyticOnNhd

end Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate
