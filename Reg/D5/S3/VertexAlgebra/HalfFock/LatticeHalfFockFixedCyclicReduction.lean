import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockFixedCyclicReduction
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

/-! Source-bound observation of the actual current-after-coefficient product. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockFixedCyclicReduction

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockParityT LatticeInvolution
open _root_.D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
open _root_.D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockFixedCyclicReduction
open Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation (hyperbolic hyperbolic_unit)
open TwistedGround.OriginalFourMChargeCoset (oscillatorCoordinate oscillatorCoordinate_tmul)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily LeanInformationAudit
open scoped TensorProduct VertexOperator

open private current_coeff from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

noncomputable section

abbrev Parameters :=
  Σ data : {D : LatticeData // IsUnit D.G.det},
    Σ _ : Fin data.val.rank, Σ _ : Carrier data.val, Σ _ : ℤ, ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun p => paritySpace p.1.val p.1.property (-1)) (fun p => ActualTensor p.1.val p.1.property)

def actual : Realization signature := realize signature
  (fun _ p x =>
    let data := p.1
    let i := p.2.1
    let b := p.2.2.1
    let k := p.2.2.2.1
    let e := p.2.2.2.2
    LatticeHalfFock.tensorCurrent data.val (ActualGround data.val data.property) i k
      ((correctedField data.val data.property b).coeff e x.val))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (data : {D : LatticeData // IsUnit D.G.det})
    (i : Fin data.val.rank) (b : Carrier data.val) (_hb : theta data.val b = -b)
    (k e : ℤ) (x : paritySpace data.val data.property (-1)),
    ∃ y : paritySpace data.val data.property (-1),
      y.val = readout.readout () ⟨data, i, b, k, e⟩ x ∧
      y ∈ Submodule.span ℂ (Set.range (fun index : FixedCarrier data.val × ℤ =>
        ((fixedParitySlice data.val data.property (-1) index.1)[[index.2]]) x))

theorem source_bridge :
    (type_of% (@current_after_odd_coeff_mem_fixedParitySlice_span)) ↔ arena.Law actual :=
  Iff.rfl

private def probeGround : ActualGround hyperbolic hyperbolic_unit := fun _ => 1

private def probeAxis : Fin hyperbolic.rank := ⟨0, by decide⟩

private def evenTensor (D : LatticeData) (hu : IsUnit D.G.det) : ActualTensor D hu :=
  (1 : Oscillator D) ⊗ₜ[ℂ] (fun _ => 1)

private def rejected : Realization signature := realize signature
  (fun _ p _ => evenTensor p.1.val p.1.property)
  (fun empty => nomatch empty)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨y, hy, _⟩ := law ⟨hyperbolic, hyperbolic_unit⟩ probeAxis 0 (by simp) 0 0 0
  let v := evenTensor hyperbolic hyperbolic_unit
  have hy' : y.val = v := hy
  have parity := y.property
  rw [hy'] at parity
  simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    neg_one_smul, LinearMap.neg_apply, LinearMap.id_apply] at parity
  have fixed : actualParity hyperbolic hyperbolic_unit v = v := by
    simp [v, evenTensor, actualParity, sigmaLinear]
  rw [fixed] at parity
  have measured := congrArg (oscillatorCoordinate hyperbolic hyperbolic_unit) parity
  have impossible : (1 : Oscillator hyperbolic) = -1 := by
    simpa [v, evenTensor, oscillatorCoordinate_tmul] using measured
  exact (by norm_num : (1 : ℂ) ≠ -1)
    (by simpa using congrArg (MvPolynomial.eval (fun _ : Index hyperbolic => (1 : ℂ))) impossible)

private def oddTensor : paritySpace hyperbolic hyperbolic_unit (-1) :=
  ⟨MvPolynomial.X (probeAxis, (0 : ℕ)) ⊗ₜ[ℂ] probeGround, by
    simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      neg_one_smul, LinearMap.neg_apply, LinearMap.id_apply, actualParity, TensorProduct.map_tmul]
    change sigma hyperbolic (MvPolynomial.X _) ⊗ₜ[ℂ] probeGround = _
    rw [sigma_X, TensorProduct.neg_tmul]⟩

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  let i := probeAxis
  let b := neutralMode hyperbolic i (-1) (LatticeAllStateField.vacuum hyperbolic)
  refine ⟨⟨⟨hyperbolic, hyperbolic_unit⟩, i, b, -1, -1⟩, oddTensor, 0, ?_⟩
  intro equality
  let A := LatticeHalfFock.tensorCurrent hyperbolic (ActualGround hyperbolic hyperbolic_unit) i (-1)
  change A ((correctedField hyperbolic hyperbolic_unit b).coeff (-1) oddTensor.val) =
    A ((correctedField hyperbolic hyperbolic_unit b).coeff (-1) 0) at equality
  have current : (correctedField hyperbolic hyperbolic_unit b).coeff (-1) oddTensor.val =
      A oddTensor.val := by
    simpa only [b, A, show -2 * (-1 : ℤ) - 3 = -1 by decide] using
      current_coeff hyperbolic hyperbolic_unit i (-1) oddTensor.val
  rw [current, map_zero, map_zero] at equality
  have measured := congrArg (oscillatorCoordinate hyperbolic hyperbolic_unit) equality
  have impossible :
      MvPolynomial.X (i, (0 : ℕ)) *
        (MvPolynomial.X (i, (0 : ℕ)) * MvPolynomial.X (i, (0 : ℕ))) =
          (0 : Oscillator hyperbolic) := by
    simp [A, i, oddTensor, probeGround, LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
      LatticeHalfFock.current, oscillatorCoordinate_tmul] at measured
  exact one_ne_zero (α := ℂ)
    (by simpa using congrArg (MvPolynomial.eval (fun _ : Index hyperbolic => (1 : ℂ))) impossible)

def familyRegistration :
    Registration arena (type_of% (@current_after_odd_coeff_mem_fixedParitySlice_span)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp current_after_odd_coeff_mem_fixedParitySlice_span,
    rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@current_after_odd_coeff_mem_fixedParitySlice_span)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str ``current_after_odd_coeff_mem_fixedParitySlice_span "__information_unit"
  realizationName := ``familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockFixedCyclicReduction
    definition := none
    coordinates := #[0, 1, 2, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end
end Reg.D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockFixedCyclicReduction
