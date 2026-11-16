import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
noncomputable section
open scoped BigOperators Topology ENNReal
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianResolvent OriginalGaussianExternalResolvent
open OriginalGaussianDifferentiation OriginalGaussianAllIndexResolvent
open OriginalGaussianExternalEvolution OriginalGaussianExternalNormal
open OriginalGaussianExternalGeneratedSource OriginalGaussianExternalRadialSums
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
private theorem pairDependence :
    ObservationalDependence pairSeriesSignature pairSeriesActual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hf : HasSum (fun _ : ℕ × ℕ => (1 : ℂ)) 0 := Eq.mp h hasSum_zero
  have he : (1 : ℂ) = 0 := by simpa only [summable_const_iff] using hf.summable
  exact one_ne_zero he
namespace kernelMode_radial_derivative
abbrev arena : Arena where
  signature := pairSeriesSignature
  Law R := ∀ (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1),
    pairSumObserve R (fun pq : ℕ × ℕ =>
      deriv (fun t : ℝ => externalT out pq.1 out' pq.2 (Real.sqrt t : ℂ)) r *
        u ^ pq.1 * v ^ pq.2)
      (deriv (fun t : ℝ => kernelMode true out out' u v (Real.sqrt t : ℂ)) r)
private theorem rejected_fails : ¬ arena.Law pairSeriesRejected := by
  intro h
  have hh := h false false (u := 0) (v := 0) (r := 1/4) (by norm_num) (by norm_num) (by norm_num)
  change False at hh
  exact hh
def family : Registration arena (type_of% (@kernelMode_radial_derivative)) where
  actual := pairSeriesActual
  bridge := Iff.rfl
  variation := ⟨@kernelMode_radial_derivative, pairSeriesRejected, rejected_fails⟩
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
    (@kernelMode_radial_derivative) (Realization pairSeriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums.kernelMode_radial_derivative.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums.kernelMode_radial_derivative.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
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
end kernelMode_radial_derivative
end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
