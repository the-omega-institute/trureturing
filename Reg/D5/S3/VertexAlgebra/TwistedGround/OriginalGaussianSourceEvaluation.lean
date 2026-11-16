import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
noncomputable section
open scoped BigOperators Topology ENNReal
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianDifferentiation
open OriginalGaussianWeightedResolvent
open OriginalGaussianAllIndexResolvent OriginalGaussianExternalResolvent
open OriginalGaussianSourceMeans OriginalGaussianSourceEvaluation
open OriginalGaussianExternalFrequency OriginalGaussianExternalDisplacement
open OriginalGaussianExternalMoments OriginalGaussianExternalRadial
open OriginalGaussianExternalEvolution OriginalGaussianExternalSourceJet
open OriginalGaussianExternalNormal OriginalGaussianExternalGenerators
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
open OriginalGaussianSourceEvaluation
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation
local notation:50 a:51 " ≋[" R "] " b:51 => Realization.readout R () _ a b
local notation:50 a:51 " ≼[" R "] " b:51 => Realization.readout R () () a b

abbrev boundSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def boundActual : Realization boundSignature := realize _ (fun _ _ a b => a ≤ b) (fun e => nomatch e)
def boundRejected : Realization boundSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem boundDependence : ObservationalDependence boundSignature boundActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (0 : ℝ) ≤ 0 := le_rfl
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) he
  norm_num at hf

abbrev seriesSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℂ (fun _ => ℕ → ℂ) (fun _ => Prop)
def seriesActual : Realization seriesSignature :=
  realize _ (fun _ a f => HasSum f a) (fun e => nomatch e)
def seriesRejected : Realization seriesSignature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)
def sumObserve (R : Realization seriesSignature) (f : ℕ → ℂ) (a : ℂ) : Prop := R.readout () a f
private theorem seriesDependence : ObservationalDependence seriesSignature seriesActual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hf : HasSum (fun _ : ℕ => (1 : ℂ)) 0 := Eq.mp h (hasSum_zero)
  have he : (1 : ℂ) = 0 := by simpa only [summable_const_iff] using hf.summable
  exact one_ne_zero he

namespace external_parameter_bound
abbrev arena : Arena where
  signature := boundSignature
  Law R := ∀ (out : Bool) (p : ℕ),
    ‖(if out then (p : ℂ) + 1 / 2 else -(p : ℂ) - 1 / 2)‖ ≼[R] (p + 1 : ℝ)
private theorem rejected_fails : ¬ arena.Law boundRejected := by
  intro h
  exact h false 0
def family : Registration arena (type_of% (@external_parameter_bound)) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨@external_parameter_bound, boundRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨boundRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := boundDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@external_parameter_bound) (Realization boundSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation.external_parameter_bound.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation.external_parameter_bound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundSignature boundActual.readout boundActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation
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
end external_parameter_bound


namespace sourceAmplitude_hasSum
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ (out : Bool) (p : ℕ) {x : ℂ} (hx : ‖x‖ < 1),
    sumObserve R (fun s : ℕ => (-1 : ℂ) ^ s * externalBinomial out p s * x ^ s *
      shiftedCentralSeries x s) (sourceAmplitude out p x)
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact h false 0 (x := 0) (by norm_num)
def family : Registration arena (type_of% (@sourceAmplitude_hasSum)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@sourceAmplitude_hasSum, seriesRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seriesRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := seriesDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceAmplitude_hasSum) (Realization seriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation.sourceAmplitude_hasSum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation.sourceAmplitude_hasSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seriesSignature seriesActual.readout seriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceAmplitude_hasSum


namespace sourceExternal_evaluation
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ) {z : ℂ} (hz : ‖z‖ < 1),
    1 - sourceExternal out p z ≋[R] sourceAmplitude out p (z ^ 2) / period (z ^ 2)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h false 0 (z := 0) (by norm_num)
def family : Registration arena (type_of% (@sourceExternal_evaluation)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@sourceExternal_evaluation, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceExternal_evaluation) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation.sourceExternal_evaluation.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation.sourceExternal_evaluation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation
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
end sourceExternal_evaluation

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation
