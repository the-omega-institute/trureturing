import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows
import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
noncomputable section
open scoped BigOperators Topology ENNReal
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianExternalResolvent
open OriginalGaussianExternalFrequency OriginalGaussianExternalFrequencyRows
open OriginalGaussianExternalDisplacement
open OriginalGaussianExternalGeneratedSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows
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

namespace external_frequency_row
abbrev arena : Arena where
  signature := seriesSignature
  Law R := ∀ (square out out' : Bool) (q : ℕ) {u z : ℂ},
    ‖u‖ + ‖z‖ < 1 →
    let K := fun p : ℕ =>
      if square then externalT out p out' q z else externalJ out p out' q z
    let C := if square then externalT false 0 out' q z else externalJ false 0 out' q z
    sumObserve R
      (fun p : ℕ => modeScale out u * externalParameter out p *
        ((if square then externalT out p out' q z else externalJ out p out' q z) -
          (if square then externalT (predecessor out p).1 (predecessor out p).2 out' q z
            else externalJ (predecessor out p).1 (predecessor out p).2 out' q z)) * u ^ p)
      (if out then
        u * (1 - u) * deriv (fun w : ℂ => ∑' p : ℕ,
          (if square then externalT out p out' q z else externalJ out p out' q z) * w ^ p) u +
          (1 - 3 * u) / 2 * (∑' p : ℕ,
            (if square then externalT out p out' q z else externalJ out p out' q z) * u ^ p) -
          (if square then externalT false 0 out' q z else externalJ false 0 out' q z) / 2
      else
        u * (1 - u) * deriv (fun w : ℂ => ∑' p : ℕ,
          (if square then externalT out p out' q z else externalJ out p out' q z) * w ^ p) u -
          (u + 1) / 2 * (∑' p : ℕ,
            (if square then externalT out p out' q z else externalJ out p out' q z) * u ^ p) +
          (if square then externalT false 0 out' q z else externalJ false 0 out' q z) / 2)
private theorem rejected_fails : ¬ arena.Law seriesRejected := by
  intro h
  exact h false false false 0 (u := 0) (z := 0) (by norm_num)
def family : Registration arena (type_of% (@external_frequency_row)) where
  actual := seriesActual
  bridge := Iff.rfl
  variation := ⟨@external_frequency_row, seriesRejected, rejected_fails⟩
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
    (@external_frequency_row) (Realization seriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows.external_frequency_row.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows.external_frequency_row.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows
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
end external_frequency_row
private theorem pairDependence : ObservationalDependence pairSeriesSignature pairSeriesActual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hf : HasSum (fun _ : ℕ × ℕ => (1 : ℂ)) 0 := Eq.mp h (hasSum_zero)
  have he : (1 : ℂ) = 0 := by simpa only [summable_const_iff] using hf.summable
  exact one_ne_zero he

namespace external_frequency_generated
abbrev arena : Arena where
  signature := pairSeriesSignature
  Law R := ∀ (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1),
    pairSumObserve R (fun pq : ℕ × ℕ => modeScale out u *
      modeFrequency out pq.1 (fun e k =>
        if square then externalT e k out' pq.2 z else externalJ e k out' pq.2 z) *
          u ^ pq.1 * v ^ pq.2)
      (if out then
        u * (1 - u) * deriv (fun w => kernelMode square out out' w v z) u +
          (1 - 3 * u) / 2 * kernelMode square out out' u v z -
          (∑' q : ℕ, (if square then externalT false 0 out' q z
            else externalJ false 0 out' q z) * v ^ q) / 2
      else
        u * (1 - u) * deriv (fun w => kernelMode square out out' w v z) u -
          (u + 1) / 2 * kernelMode square out out' u v z +
          (∑' q : ℕ, (if square then externalT false 0 out' q z
            else externalJ false 0 out' q z) * v ^ q) / 2)
private theorem rejected_fails : ¬ arena.Law pairSeriesRejected := by
  intro h
  exact h false false false (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@external_frequency_generated)) where
  actual := pairSeriesActual
  bridge := Iff.rfl
  variation := ⟨@external_frequency_generated, pairSeriesRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pairSeriesRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := pairDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@external_frequency_generated) (Realization pairSeriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows.external_frequency_generated.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows.external_frequency_generated.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows
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
end external_frequency_generated

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows
