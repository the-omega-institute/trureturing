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
open OriginalGaussianExternalGenerators
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
local notation:50 a:51 " ≋[" R "] " b:51 => Realization.readout R () _ a b
local notation:50 a:51 " ≼[" R "] " b:51 => Realization.readout R () () a b

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

namespace sourceAmplitude_mode_hasSum
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ (out : Bool) {u x : ℂ}
    (hsmall : ‖u‖ + ‖x‖ < 1),
    sumObserve R (fun p : ℕ => sourceAmplitude out p x * u ^ p)
      (∑' n : ℕ, ∑' p : ℕ, amplitudeTerm out u x (p, n))
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact h false (u := 0) (x := 0) (by norm_num)
def family : Registration arena (type_of% (@sourceAmplitude_mode_hasSum)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@sourceAmplitude_mode_hasSum, seriesRejected, rejected_fails⟩
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
    (@sourceAmplitude_mode_hasSum) (Realization seriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators.sourceAmplitude_mode_hasSum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators.sourceAmplitude_mode_hasSum.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
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
end sourceAmplitude_mode_hasSum


namespace sourceAmplitude_positive_generator
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ {u x : ℂ}
    (hsmall : ‖u‖ + ‖x‖ < 1),
    sumObserve R (fun p : ℕ => sourceAmplitude true p x * u ^ p)
      ((1 / (1 - u)) * centralGenerating (-x * u / (1 - u)))
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact h (u := 0) (x := 0) (by norm_num)
def family : Registration arena (type_of% (@sourceAmplitude_positive_generator)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@sourceAmplitude_positive_generator, seriesRejected, rejected_fails⟩
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
    (@sourceAmplitude_positive_generator) (Realization seriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators.sourceAmplitude_positive_generator.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators.sourceAmplitude_positive_generator.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
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
end sourceAmplitude_positive_generator


namespace sourceAmplitude_negative_generator
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ {u x : ℂ}
    (hsmall : ‖u‖ + ‖x‖ < 1),
    sumObserve R (fun p : ℕ => sourceAmplitude false p x * u ^ p)
      ((1 / (1 - u)) * centralGenerating (x / (1 - u)))
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact h (u := 0) (x := 0) (by norm_num)
def family : Registration arena (type_of% (@sourceAmplitude_negative_generator)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@sourceAmplitude_negative_generator, seriesRejected, rejected_fails⟩
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
    (@sourceAmplitude_negative_generator) (Realization seriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators.sourceAmplitude_negative_generator.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators.sourceAmplitude_negative_generator.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
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
end sourceAmplitude_negative_generator


namespace sourceAmplitude_generators
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1),
    sumObserve R (fun p : ℕ => sourceAmplitude true p x * u ^ p)
      ((1 / (1 - u)) * (1 + x * u / (1 - u)) ^ (-1 / 2 : ℂ)) ∧
    HasSum (fun p : ℕ => sourceAmplitude false p x * u ^ p)
      ((1 / (1 - u)) * (1 - x / (1 - u)) ^ (-1 / 2 : ℂ))
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact (h (u := 0) (x := 0) (by norm_num)).1
def family : Registration arena (type_of% (@sourceAmplitude_generators)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@sourceAmplitude_generators, seriesRejected, rejected_fails⟩
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
    (@sourceAmplitude_generators) (Realization seriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators.sourceAmplitude_generators.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators.sourceAmplitude_generators.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
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
end sourceAmplitude_generators


namespace sourceMode_square
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1),
    sourceMode true u x ^ 2 ≋[R] 1 / ((1 - u) * (1 - (1 - x) * u)) ∧
    sourceMode false u x ^ 2 = 1 / ((1 - u) * (1 - x - u))
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h (u := 0) (x := 0) (by norm_num)).1
def family : Registration arena (type_of% (@sourceMode_square)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@sourceMode_square, eqRejected, rejected_fails⟩
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
    (@sourceMode_square) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators.sourceMode_square.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators.sourceMode_square.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceMode_square




end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
