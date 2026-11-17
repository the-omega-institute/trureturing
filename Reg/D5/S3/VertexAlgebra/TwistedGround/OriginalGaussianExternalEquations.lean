import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations
import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows
/-! Faithful actual frequency and displacement readouts. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianExternalResolvent OriginalGaussianExternalFrequency
open OriginalGaussianExternalGeneratedSource OriginalGaussianExternalEquations
open OriginalGaussianExternalDisplacement OriginalGaussianExternalGenerators OriginalGaussianAllIndexResolvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations
private theorem pairDependence : ObservationalDependence pairSeriesSignature pairSeriesActual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hf : HasSum (fun _ : ℕ × ℕ => (1 : ℂ)) 0 := Eq.mp h hasSum_zero
  have he : (1 : ℂ) = 0 := by simpa only [summable_const_iff] using hf.summable
  exact one_ne_zero he

namespace second_frequency
abbrev arena : Arena where
  signature := pairSeriesSignature
  Law R := ∀ (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1),
    pairSumObserve R (fun pq : ℕ × ℕ => modeScale out' v *
      modeFrequency out' pq.2 (fun e k =>
        if square then externalT out pq.1 e k z else externalJ out pq.1 e k z) *
          u ^ pq.1 * v ^ pq.2)
      (secondModeDerivative square out out' u v z - modeB out' *
        (∑' p : ℕ, (if square then externalT false 0 out p z
          else externalJ false 0 out p z) * u ^ p))
private theorem rejected_fails : ¬ arena.Law pairSeriesRejected := by
  intro h
  exact h false false false (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@second_frequency)) where
  actual := pairSeriesActual
  bridge := Iff.rfl
  variation := ⟨@second_frequency, pairSeriesRejected, rejected_fails⟩
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
    (@second_frequency) (Realization pairSeriesSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations.second_frequency.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations.second_frequency.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations
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
end second_frequency

namespace displacement_with_boundary
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1),
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lam := shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    let B := fun (sq e : Bool) (w : ℂ) => ∑' k : ℕ,
      (if sq then externalT false 0 e k z else externalJ false 0 e k z) * w ^ k
    let U := fun e w => sourceMode e w x * modeA e w x -
      modeB e * OriginalGaussianSourceEvaluation.sourceAmplitude false 0 x
    let V := fun e w => sourceMode e w x * modeH e w x lam +
      modeB e * OriginalGaussianSourceEvaluation.sourceAmplitude false 0 x
    (R.readout () ℂ (modeScale out' v * (firstModeDerivative false out out' u v z - modeB out * B false out' v) +
      modeScale out u * (secondModeDerivative false out out' u v z - modeB out' * B false out u)) (
        (1 - x) * (U out u * V out' v + V out u * U out' v) / 2)) ∧
    (modeScale out' v * (firstModeDerivative true out out' u v z - modeB out * B true out' v) -
      modeScale out u * (secondModeDerivative true out out' u v z - modeB out' * B true out u) =
        (1 - x) * (U out u * V out' v - V out u * U out' v) / 2)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  have hs : Real.sqrt (1 / 4 : ℝ) < 1 := by
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by norm_num)
  exact (h false false (u := 0) (v := 0) (r := 1/4) (by norm_num) (by norm_num)
    (by simpa using hs) (by simpa using hs)).1
def family : Registration arena (type_of% (@displacement_with_boundary)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@displacement_with_boundary, eqRejected, rejected_fails⟩
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
    (@displacement_with_boundary) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations.displacement_with_boundary.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations.displacement_with_boundary.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations
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
end displacement_with_boundary

namespace displacement_differential
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1),
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lam := shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    (R.readout () ℂ (modeScale out' v * firstModeDerivative false out out' u v z +
      modeScale out u * secondModeDerivative false out out' u v z) (
        (1 - x) * sourceMode out u x * sourceMode out' v x *
          (modeA out u x * modeH out' v x lam + modeH out u x lam * modeA out' v x) / 2 +
            modeB out * modeB out')) ∧
    (modeScale out' v * firstModeDerivative true out out' u v z -
      modeScale out u * secondModeDerivative true out out' u v z =
        (1 - x) * sourceMode out u x * sourceMode out' v x *
          (modeA out u x * modeH out' v x lam - modeH out u x lam * modeA out' v x) / 2)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  have hs : Real.sqrt (1 / 4 : ℝ) < 1 := by
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by norm_num)
  exact (h false false (u := 0) (v := 0) (r := 1/4) (by norm_num) (by norm_num)
    (by simpa using hs) (by simpa using hs)).1
def family : Registration arena (type_of% (@displacement_differential)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@displacement_differential, eqRejected, rejected_fails⟩
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
    (@displacement_differential) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations.displacement_differential.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations.displacement_differential.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations
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
end displacement_differential
namespace literal_symmetry
abbrev arena : Arena where
  signature := _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric.complexSignature
  Law R := ∀ (square out out' : Bool) (p q : ℕ) {z : ℂ} (_hz : ‖z‖<1),
    R.readout () ()
      (if square then externalT out p out' q z else externalJ out p out' q z)
      (if square then externalT out' q out p z else externalJ out' q out p z)

private theorem rejected_fails : ¬ arena.Law _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric.complexFalse := by
  intro h
  exact h true true true 0 0 (z := 0) (by simp)

def family : Registration arena (type_of% (@literal_symmetry)) where
  actual := _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric.complexEqual
  bridge := Iff.rfl
  variation := ⟨@literal_symmetry, _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric.complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric.complexEqual _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric.complexFalse rejected_fails
  dependence := _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric.complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_symmetry) (Realization _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric.complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations.literal_symmetry.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations.literal_symmetry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric.complexSignature _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric.complexEqual.readout _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric.complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations
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
end literal_symmetry

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations
