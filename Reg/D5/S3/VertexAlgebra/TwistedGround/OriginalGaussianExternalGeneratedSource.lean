import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
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
open OriginalGaussianExternalModeSums OriginalGaussianExternalJetSums
open OriginalGaussianExternalGeneratedSource
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
open OriginalGaussianExternalGeneratedSource
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
local notation:50 a:51 " ≋[" R "] " b:51 => Realization.readout R () _ a b
local notation:50 a " ≼[" R "] " b => Realization.readout R () () a b

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

abbrev pairSeriesSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℂ (fun _ => (ℕ × ℕ) → ℂ) (fun _ => Prop)
def pairSeriesActual : Realization pairSeriesSignature :=
  realize _ (fun _ a f => HasSum f a) (fun e => nomatch e)
def pairSeriesRejected : Realization pairSeriesSignature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)
def pairSumObserve (R : Realization pairSeriesSignature) (f : (ℕ × ℕ) → ℂ) (a : ℂ) : Prop := R.readout () a f
private theorem pairSeriesDependence : ObservationalDependence pairSeriesSignature pairSeriesActual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hf : HasSum (fun _ : ℕ × ℕ => (1 : ℂ)) 0 := Eq.mp h (hasSum_zero)
  have he : (1 : ℂ) = 0 := by simpa only [summable_const_iff] using hf.summable
  exact one_ne_zero he


namespace external_displacement_generated
abbrev arena : Arena where
  signature := pairSeriesSignature
  Law R := ∀ (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hu : ‖u‖ + r < 1) (hv : ‖v‖ + r < 1),
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    let U := fun e w => sourceMode e w x * modeA e w x -
      modeB e * sourceAmplitude false 0 x
    let V := fun e w => sourceMode e w x * modeH e w x lambdaRatio +
      modeB e * sourceAmplitude false 0 x
    pairSumObserve R (fun pq : ℕ × ℕ => modeScale out u * modeScale out' v *
      (modeFrequency out pq.1 (fun e k => externalJ e k out' pq.2 z) +
        modeFrequency out' pq.2 (fun e k => externalJ out pq.1 e k z)) *
          u ^ pq.1 * v ^ pq.2)
      ((1 - x) * (U out u * V out' v + V out u * U out' v) / 2) ∧
    HasSum (fun pq : ℕ × ℕ => modeScale out u * modeScale out' v *
      (modeFrequency out pq.1 (fun e k => externalT e k out' pq.2 z) -
        modeFrequency out' pq.2 (fun e k => externalT out pq.1 e k z)) *
          u ^ pq.1 * v ^ pq.2)
      ((1 - x) * (U out u * V out' v - V out u * U out' v) / 2)
private theorem rejected_fails : ¬ arena.Law pairSeriesRejected := by
  intro h
  exact (h false false (u := 0) (v := 0) (r := 1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@external_displacement_generated)) where
  actual := pairSeriesActual
  bridge := Iff.rfl
  variation := ⟨@external_displacement_generated, pairSeriesRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pairSeriesRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := pairSeriesDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@external_displacement_generated) (Realization pairSeriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource.external_displacement_generated.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource.external_displacement_generated.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSeriesSignature pairSeriesActual.readout pairSeriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end external_displacement_generated


namespace external_radial_generated
abbrev arena : Arena where
  signature := pairSeriesSignature
  Law R := ∀ (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hu : ‖u‖ + r < 1) (hv : ‖v‖ + r < 1),
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    let U := fun e w => sourceMode e w x * modeA e w x -
      modeB e * sourceAmplitude false 0 x
    let V := fun e w => sourceMode e w x * modeH e w x lambdaRatio +
      modeB e * sourceAmplitude false 0 x
    pairSumObserve R (fun pq : ℕ × ℕ => modeScale out u * modeScale out' v *
      (2 * x * deriv (fun t : ℝ => externalT out pq.1 out' pq.2 (Real.sqrt t : ℂ)) r -
        modeFrequency out pq.1 (fun e k => externalT e k out' pq.2 z) -
        modeFrequency out' pq.2 (fun e k => externalT out pq.1 e k z)) *
          u ^ pq.1 * v ^ pq.2)
      ((1 - x) * (V out u * V out' v - U out u * U out' v) / 2)
private theorem rejected_fails : ¬ arena.Law pairSeriesRejected := by
  intro h
  exact h false false (u := 0) (v := 0) (r := 1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@external_radial_generated)) where
  actual := pairSeriesActual
  bridge := Iff.rfl
  variation := ⟨@external_radial_generated, pairSeriesRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pairSeriesRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := pairSeriesDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@external_radial_generated) (Realization pairSeriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource.external_radial_generated.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource.external_radial_generated.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSeriesSignature pairSeriesActual.readout pairSeriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end external_radial_generated


namespace external_negative_zero_generated
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ (out : Bool) {u : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hu : ‖u‖ + r < 1),
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    sumObserve R (fun p : ℕ => modeScale out u * externalJ false 0 out p z * u ^ p)
      ((Real.sqrt (1 - r) : ℂ) / 2 *
        (sourceMode out u x * (modeH out u x lambdaRatio - modeA out u x)) + modeB out) ∧
    HasSum (fun p : ℕ => modeScale out u * externalT false 0 out p z * u ^ p)
      ((Real.sqrt (1 - r) : ℂ) / 2 *
        (sourceMode out u x * (modeH out u x lambdaRatio + modeA out u x)))
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact (h false (u := 0) (r := 1/2) (by norm_num) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@external_negative_zero_generated)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@external_negative_zero_generated, seriesRejected, rejected_fails⟩
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
    (@external_negative_zero_generated) (Realization seriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource.external_negative_zero_generated.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource.external_negative_zero_generated.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end external_negative_zero_generated

namespace kernelMode_derivative
abbrev arena : Arena where
  signature := pairSeriesSignature
  Law R := ∀ (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1),
    pairSumObserve R (fun pq : ℕ × ℕ => (pq.1 : ℂ) *
      (if square then externalT out pq.1 out' pq.2 z else externalJ out pq.1 out' pq.2 z) *
        u ^ (pq.1 - 1) * v ^ pq.2)
      (deriv (fun w => kernelMode square out out' w v z) u)
private theorem rejected_fails : ¬ arena.Law pairSeriesRejected := by
  intro h
  exact h false false false (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@kernelMode_derivative)) where
  actual := pairSeriesActual
  bridge := Iff.rfl
  variation := ⟨@kernelMode_derivative, pairSeriesRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pairSeriesRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := pairSeriesDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernelMode_derivative) (Realization pairSeriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource.kernelMode_derivative.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource.kernelMode_derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSeriesSignature pairSeriesActual.readout pairSeriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end kernelMode_derivative

namespace boundary_normalization
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    R.readout () _ ((Real.sqrt (1 - r) : ℂ) * sourceAmplitude false 0 r) (1)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (r := 1/4) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@boundary_normalization)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@boundary_normalization, eqRejected, rejected_fails⟩
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
    (@boundary_normalization) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource.boundary_normalization.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource.boundary_normalization.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
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
end boundary_normalization
end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
