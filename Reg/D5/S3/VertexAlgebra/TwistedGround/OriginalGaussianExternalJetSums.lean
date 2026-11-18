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
open OriginalGaussianExternalJetSums
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums
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

namespace sourceJetMoment_generators
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ {u : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hsmall : ‖u‖ + r < 1),
    let x : ℂ := r
    let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    sumObserve R (fun p : ℕ => sourceJetMoment true p x * u ^ p)
      (2 * x * deriv (fun w => sourceMode true u w) x -
        sourceMode true u x * (1 - 2 * u + (1 - x) * u ^ 2) /
          (2 * (1 - (1 - x) * u)) + sourceAmplitude false 0 x / 2 -
        2 * x * sourceMode true u x * lambdaRatio) ∧
    HasSum (fun p : ℕ => u * sourceJetMoment false p x * u ^ p)
      (2 * x * u * deriv (fun w => sourceMode false u w) x -
        sourceMode false u x * (u * (1 - u) / (2 * (1 - x - u)) - 1 / 2) -
        sourceAmplitude false 0 x / 2 - 2 * x * u * sourceMode false u x * lambdaRatio)
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact (h (u := 0) (r := 1/2) (by norm_num) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@sourceJetMoment_generators)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@sourceJetMoment_generators, seriesRejected, rejected_fails⟩
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
    (@sourceJetMoment_generators) (Realization seriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums.sourceJetMoment_generators.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums.sourceJetMoment_generators.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceJetMoment_generators


namespace sourceJetMoment_generators_explicit
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ {u : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hsmall : ‖u‖ + r < 1),
    let x : ℂ := r
    let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    sumObserve R (fun p : ℕ => sourceJetMoment true p x * u ^ p)
      (sourceMode true u x *
        (-x * u / (1 - (1 - x) * u) -
          (1 - 2 * u + (1 - x) * u ^ 2) / (2 * (1 - (1 - x) * u)) - 2 * x * lambdaRatio) +
        sourceAmplitude false 0 x / 2) ∧
    HasSum (fun p : ℕ => u * sourceJetMoment false p x * u ^ p)
      (sourceMode false u x *
        (x * u / (1 - x - u) -
          (u * (1 - u) / (2 * (1 - x - u)) - 1 / 2) - 2 * x * u * lambdaRatio) -
        sourceAmplitude false 0 x / 2)
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact (h (u := 0) (r := 1/2) (by norm_num) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@sourceJetMoment_generators_explicit)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@sourceJetMoment_generators_explicit, seriesRejected, rejected_fails⟩
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
    (@sourceJetMoment_generators_explicit) (Realization seriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums.sourceJetMoment_generators_explicit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums.sourceJetMoment_generators_explicit.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceJetMoment_generators_explicit


namespace amplitude_derivative_mode
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ (out : Bool) {u x : ℂ} (_hsmall : ‖u‖ + ‖x‖ < 1),
    sumObserve R (fun p : ℕ => deriv (sourceAmplitude out p) x * u ^ p)
      (deriv (fun w => sourceMode out u w) x) ∧
    DifferentiableAt ℂ (fun w => sourceMode out u w) x ∧
    ∀ p, DifferentiableAt ℂ (sourceAmplitude out p) x
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact (h true (u := 0) (x := 0) (by norm_num)).1
def family : Registration arena (type_of% (@amplitude_derivative_mode)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@amplitude_derivative_mode, seriesRejected, rejected_fails⟩
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
    (@amplitude_derivative_mode) (Realization seriesSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums.amplitude_derivative_mode.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums.amplitude_derivative_mode.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums
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
end amplitude_derivative_mode


namespace diagonal_derivative_explicit
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) {u x : ℂ} (_hsmall : ‖u‖ + ‖x‖ < 1),
    let b : ℂ := if out then u else -1
    R.readout () _ (deriv (fun w => sourceMode out u w) x)
      (-b * sourceMode out u x / (2 * (1-u+b*x)))
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h true (u := 0) (x := 0) (by norm_num)
def family : Registration arena (type_of% (@diagonal_derivative_explicit)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@diagonal_derivative_explicit, eqRejected, rejected_fails⟩
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
    (@diagonal_derivative_explicit) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums.diagonal_derivative_explicit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums.diagonal_derivative_explicit.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums
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
end diagonal_derivative_explicit

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums
