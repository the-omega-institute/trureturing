import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
noncomputable section
open scoped BigOperators Topology ENNReal
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianResolvent OriginalGaussianExternalResolvent
open OriginalGaussianDifferentiation OriginalGaussianAllIndexResolvent
open OriginalGaussianExternalEvolution OriginalGaussianExternalNormal
open OriginalGaussianExternalGeneratedSource OriginalGaussianExternalRadialSums
open OriginalGaussianExternalGenerators
open OriginalGaussianExternalEquations
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
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
  bridge := by rfl
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

namespace radial_differential
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1),
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lam := shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    R.readout () ℂ
      (2 * x * modeScale out u * modeScale out' v *
        deriv (fun t : ℝ => kernelMode true out out' u v (Real.sqrt t : ℂ)) r -
        modeScale out' v * firstModeDerivative true out out' u v z -
        modeScale out u * secondModeDerivative true out out' u v z)
      ((1 - x) * sourceMode out u x * sourceMode out' v x *
        (modeH out u x lam * modeH out' v x lam -
          modeA out u x * modeA out' v x) / 2)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  have hs : Real.sqrt (1 / 4 : ℝ) < 1 := by
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by norm_num)
  exact h false false (u := 0) (v := 0) (r := 1 / 4)
    (by norm_num) (by norm_num) (by simpa using hs) (by simpa using hs)
def family : Registration arena (type_of% (@radial_differential)) where
  actual := eqActual
  bridge := by rfl
  variation := ⟨@radial_differential, eqRejected, rejected_fails⟩
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
    (@radial_differential) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums.radial_differential.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums.radial_differential.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end radial_differential
abbrev literalDiffSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ)
    (fun _ => ℂ → Prop)
def literalDiffActual : Realization literalDiffSignature :=
  realize _ (fun _ _ f z => DifferentiableAt ℂ f z) (fun e => nomatch e)
def literalDiffBad : Realization literalDiffSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem literalDiffDependence :
    ObservationalDependence literalDiffSignature literalDiffActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun z => z⁻¹), ?_⟩
  intro h
  have hd : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) 0 :=
    Eq.mp (congrFun h 0) (differentiableAt_const (0 : ℂ))
  exact (differentiableAt_inv_iff.mp hd) rfl

namespace literal_differentiable
abbrev arena : Arena where
  signature := literalDiffSignature
  Law R := ∀ (out out' : Bool) (p q : ℕ) {z : ℂ} (_hz : ‖z‖<1),
    R.readout () () (externalT out p out' q) z

private theorem rejected_fails : ¬ arena.Law literalDiffBad := by
  intro h
  exact h true true 0 0 (z := 0) (by simp)

def family : Registration arena (type_of% (@literal_differentiable)) where
  actual := literalDiffActual
  bridge := Iff.rfl
  variation := ⟨@literal_differentiable, literalDiffBad, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law literalDiffActual literalDiffBad rejected_fails
  dependence := literalDiffDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_differentiable) (Realization literalDiffSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums.literal_differentiable.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums.literal_differentiable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize literalDiffSignature literalDiffActual.readout literalDiffActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end literal_differentiable

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
