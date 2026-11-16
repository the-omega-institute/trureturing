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
open OriginalGaussianExternalMoments
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments
local notation:50 a:51 " ≋[" R "] " b:51 => Realization.readout R () _ a b
local notation:50 a:51 " ≼[" R "] " b:51 => Realization.readout R () () a b

namespace sourceMoment_eq_modeFrequency
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ) {x : ℂ} (hx : ‖x‖ < 1),
    sourceMoment out p x ≋[R] modeFrequency out p (fun e k => sourceAmplitude e k x)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h false 0 (x := 0) (by norm_num)
def family : Registration arena (type_of% (@sourceMoment_eq_modeFrequency)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@sourceMoment_eq_modeFrequency, eqRejected, rejected_fails⟩
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
    (@sourceMoment_eq_modeFrequency) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments.sourceMoment_eq_modeFrequency.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments.sourceMoment_eq_modeFrequency.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments
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
end sourceMoment_eq_modeFrequency


namespace source_moment_pairings
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1),
    (sourceBilinearFunctional (externalVector out p (Real.sqrt r : ℂ))
      (oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1)) ≋[R]         -(Real.sqrt (1 - r) : ℂ) * sourceMoment out p (r : ℂ)) ∧
    (sourceBilinearFunctional (externalVector out p (Real.sqrt r : ℂ))
      (resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1)) =
        -(Real.sqrt (1 - r) : ℂ) * sourceJetMoment out p (r : ℂ))
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h false 0 (r := 1/2) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@source_moment_pairings)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@source_moment_pairings, eqRejected, rejected_fails⟩
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
    (@source_moment_pairings) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments.source_moment_pairings.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments.source_moment_pairings.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments
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
end source_moment_pairings


namespace external_displacement_explicit
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    let z : ℂ := Real.sqrt r
    (modeFrequency out p (fun e k => externalJ e k out' q z) +
      modeFrequency out' q (fun e k => externalJ out p e k z) ≋[R]       (1 - (r : ℂ)) * (sourceMoment out p r * sourceJetMoment out' q r +
        sourceJetMoment out p r * sourceMoment out' q r) / 2) ∧
    (modeFrequency out p (fun e k => externalT e k out' q z) -
      modeFrequency out' q (fun e k => externalT out p e k z) =
      (1 - (r : ℂ)) * (sourceMoment out p r * sourceJetMoment out' q r -
        sourceJetMoment out p r * sourceMoment out' q r) / 2)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h false 0 false 0 (r := 1/2) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@external_displacement_explicit)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@external_displacement_explicit, eqRejected, rejected_fails⟩
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
    (@external_displacement_explicit) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments.external_displacement_explicit.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments.external_displacement_explicit.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end external_displacement_explicit

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments
