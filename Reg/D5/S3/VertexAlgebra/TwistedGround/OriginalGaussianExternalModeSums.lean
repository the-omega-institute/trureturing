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
open OriginalGaussianExternalModeSums
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalModeSums
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

namespace sourceMoment_generators
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1),
    sumObserve R (fun p : ℕ => sourceMoment true p x * u ^ p)
      (u * (1 - u) * deriv (fun w => sourceMode true w x) u +
        (1 - 3 * u) / 2 * sourceMode true u x - sourceAmplitude false 0 x / 2) ∧
    HasSum (fun p : ℕ => u * sourceMoment false p x * u ^ p)
      (u * (1 - u) * deriv (fun w => sourceMode false w x) u -
        (u + 1) / 2 * sourceMode false u x + sourceAmplitude false 0 x / 2)
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact (h (u := 0) (x := 0) (by norm_num)).1
def family : Registration arena (type_of% (@sourceMoment_generators)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@sourceMoment_generators, seriesRejected, rejected_fails⟩
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
    (@sourceMoment_generators) (Realization seriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalModeSums.sourceMoment_generators.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalModeSums.sourceMoment_generators.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalModeSums
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceMoment_generators


namespace sourceMoment_generators_explicit
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1),
    sumObserve R (fun p : ℕ => sourceMoment true p x * u ^ p)
      (sourceMode true u x * (1 - 2 * u + (1 - x) * u ^ 2) /
        (2 * (1 - (1 - x) * u)) - sourceAmplitude false 0 x / 2) ∧
    HasSum (fun p : ℕ => u * sourceMoment false p x * u ^ p)
      (sourceMode false u x * (u * (1 - u) / (2 * (1 - x - u)) - 1 / 2) +
        sourceAmplitude false 0 x / 2)
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact (h (u := 0) (x := 0) (by norm_num)).1
def family : Registration arena (type_of% (@sourceMoment_generators_explicit)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@sourceMoment_generators_explicit, seriesRejected, rejected_fails⟩
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
    (@sourceMoment_generators_explicit) (Realization seriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalModeSums.sourceMoment_generators_explicit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalModeSums.sourceMoment_generators_explicit.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalModeSums
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceMoment_generators_explicit

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalModeSums
