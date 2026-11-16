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
open OriginalGaussianExternalFrequency
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency
local notation:50 a:51 " ≋[" R "] " b:51 => Realization.readout R () _ a b
local notation:50 a:51 " ≼[" R "] " b:51 => Realization.readout R () () a b

namespace binomial_frequency
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p s : ℕ),
    (s : ℂ) * externalBinomial out p s ≋[R] externalParameter out p *
      (externalBinomial out p s -
        externalBinomial (predecessor out p).1 (predecessor out p).2 s)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h false 0 0
def family : Registration arena (type_of% (@binomial_frequency)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@binomial_frequency, eqRejected, rejected_fails⟩
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
    (@binomial_frequency) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency.binomial_frequency.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency.binomial_frequency.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency
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
end binomial_frequency


namespace frequencyVector_apply
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) (n : ℕ),
    frequencyVector out p z n ≋[R] (n + 1 : ℂ) * externalColumn out p z n
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h false 0 (z := 0) (by norm_num) 0
def family : Registration arena (type_of% (@frequencyVector_apply)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@frequencyVector_apply, eqRejected, rejected_fails⟩
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
    (@frequencyVector_apply) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency.frequencyVector_apply.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency.frequencyVector_apply.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency
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
end frequencyVector_apply


namespace externalVector_negative_zero
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {z : ℂ} (hz : ‖z‖ < 1),
    externalVector false 0 z ≋[R] -sourceFamily 1 z
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (z := 0) (by norm_num)
def family : Registration arena (type_of% (@externalVector_negative_zero)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@externalVector_negative_zero, eqRejected, rejected_fails⟩
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
    (@externalVector_negative_zero) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency.externalVector_negative_zero.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency.externalVector_negative_zero.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency
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
end externalVector_negative_zero

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency
