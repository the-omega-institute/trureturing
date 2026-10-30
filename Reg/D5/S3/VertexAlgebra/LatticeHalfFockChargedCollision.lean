import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
  LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
  LatticeHalfFockChargedCollision
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
open scoped TensorProduct VertexOperator

noncomputable section

private theorem creation_zero : creationCoeff hyperbolic 0 0 = 1 := by
  have series : creationSeries hyperbolic 0 = 0 := by
    ext n
    simp [creationSeries]
  simp [creationCoeff, creationExponential, series,
    PowerSeries.subst_zero_eq_C_constantCoeff]

private theorem source_probe :
    (((LatticeAllStateField.Y hyperbolic
      (Finsupp.single 0 (1 : Oscillator hyperbolic)))[[-1]])
      (Finsupp.single 0 (1 : Oscillator hyperbolic))) = probeSource := by
  rw [LatticeAllStateField.stateField_ground]
  change rawCoeff hyperbolic 0 0 (Finsupp.single 0 1) = _
  rw [LatticeActualOrderedProducts.raw_ground]
  simp [bilinear, epsilon, paritySign, lowerCocycleExponent,
    creation_zero, probeSource]

abbrev BoundData := { D : LatticeData // IsUnit D.G.det }

namespace Taylor

abbrev Parameter := Σ data : BoundData, Charge data.val × Charge data.val × ℕ × ℤ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun p => ActualTensor p.1.val p.1.property)
  (fun p => ActualTensor p.1.val p.1.property)

def actual : Realization signature := realize signature
  (fun _ p x => (correctedField p.1.val p.1.property
      (Finsupp.single (p.2.1 + p.2.2.1)
        (creationCoeff p.1.val p.2.1 p.2.2.2.1))).coeff p.2.2.2.2 x) (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) (x : ActualTensor D hu),
    readout.readout () ⟨⟨D, hu⟩, sigma, tau, N, e⟩ x =
      collisionCoefficient D hu sigma tau N e x

theorem source_bridge : (type_of% (@charged_allN_draft)) ↔ arena.Law actual := Iff.rfl

private theorem probe_nonzero :
    actual.readout () ⟨⟨hyperbolic, hyperbolic_unit⟩, 0, 0, 0, 0⟩ probeState ≠ 0 := by
  change (correctedField hyperbolic hyperbolic_unit
    (Finsupp.single (0 + 0) (creationCoeff hyperbolic 0 0))).coeff 0 probeState ≠ 0
  rw [creation_zero, add_zero]
  change (correctedField hyperbolic hyperbolic_unit probeSource).coeff 0 probeState ≠ 0
  rw [probe_source_field]
  simpa only [chargedField, HVertexOperator.coeff_of_coeff] using probe_leading

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit 0 0 (0) 0 probeState
  have good := charged_allN_draft hyperbolic hyperbolic_unit 0 0 (0) 0 probeState
  apply probe_nonzero
  exact good.trans bad.symm

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨⟨hyperbolic, hyperbolic_unit⟩, 0, 0, 0, 0⟩, 0, probeState, ?_⟩
  intro equality
  apply probe_nonzero
  exact equality.symm.trans (by simp [actual, realize])

def familyRegistration : Registration arena (type_of% (@charged_allN_draft)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp charged_allN_draft, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_allN_draft) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision.charged_allN_draft "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision.Taylor.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision
    definition := none
    coordinates := #[0, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Taylor

namespace Normalized

abbrev Parameter := Σ data : BoundData, Charge data.val × Charge data.val × ℤ × ℤ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun p => ActualTensor p.1.val p.1.property)
  (fun p => ActualTensor p.1.val p.1.property)

def actual : Realization signature := realize signature
  (fun _ p x => (correctedField p.1.val p.1.property
      (((LatticeAllStateField.Y p.1.val
        (Finsupp.single p.2.1 (1 : Oscillator p.1.val)))[[p.2.2.2.1]])
        (Finsupp.single p.2.2.1 (1 : Oscillator p.1.val)))).coeff p.2.2.2.2 x) (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (sigma tau : Charge D)
    (r : ℤ) (e : ℤ) (x : ActualTensor D hu),
    readout.readout () ⟨⟨D, hu⟩, sigma, tau, r, e⟩ x =
      if -r - 1 - bilinear D sigma tau < 0 then 0 else
        (chargeScalar D sigma * chargeScalar D tau *
          (2 : ℂ) ^ (-2 * bilinear D sigma tau)) •
          TensorProduct.map
            (collisionOscillator D sigma tau
              (-r - 1 - bilinear D sigma tau).toNat e)
            (groundAction D hu sigma * groundAction D hu tau) x

theorem source_bridge : (type_of% (@charged_normalized_source_product_allN)) ↔ arena.Law actual := Iff.rfl

private theorem probe_nonzero :
    actual.readout () ⟨⟨hyperbolic, hyperbolic_unit⟩, 0, 0, -1, 0⟩ probeState ≠ 0 := by
  change (correctedField hyperbolic hyperbolic_unit _).coeff 0 probeState ≠ 0
  rw [source_probe, probe_source_field]
  simpa only [chargedField, HVertexOperator.coeff_of_coeff] using probe_leading

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit 0 0 (-1) 0 probeState
  have good := charged_normalized_source_product_allN hyperbolic hyperbolic_unit 0 0 (-1) 0 probeState
  apply probe_nonzero
  exact good.trans bad.symm

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨⟨hyperbolic, hyperbolic_unit⟩, 0, 0, -1, 0⟩, 0, probeState, ?_⟩
  intro equality
  apply probe_nonzero
  exact equality.symm.trans (by simp [actual, realize])

def familyRegistration : Registration arena (type_of% (@charged_normalized_source_product_allN)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp charged_normalized_source_product_allN, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_normalized_source_product_allN) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision.charged_normalized_source_product_allN "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision.Normalized.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision
    definition := none
    coordinates := #[0, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Normalized

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision
