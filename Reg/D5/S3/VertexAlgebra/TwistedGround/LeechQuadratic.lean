import D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice
open _root_.D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 12 ⊕ Fin 12) (fun _ => ModTwoCharge data)

def actual : Realization signature :=
  realize signature (fun _ _ index => hyperbolicBasis index) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation :=
    (∀ index, quadratic data (observation.readout () () index) = 0) ∧
    (∀ first second, modTwoPairing data (observation.readout () () first)
      (observation.readout () () second) = if partner first = second then 1 else 0) ∧
    (∀ charge : Charge data, quadratic data (reduceCharge data charge) =
      (bilinear data charge charge / 2 : ℤ))

theorem exact_source_bridge : (type_of% (@original_plus_type)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law.2.1 (Sum.inl (0 : Fin 12)) (Sum.inr (0 : Fin 12))
  norm_num [rejected, realize, partner] at contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), Sum.inl (0 : Fin 12), Sum.inr (0 : Fin 12), ?_⟩
  change hyperbolicBasis (Sum.inl (0 : Fin 12)) ≠ hyperbolicBasis (Sum.inr (0 : Fin 12))
  exact hyperbolicBasis.injective.ne (by simp)

def familyRegistration : Registration arena (type_of% (@original_plus_type)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp original_plus_type, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_plus_type)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic.original_plus_type "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

def frameActual : Realization signature :=
  realize signature (fun _ _ index => frame index) (fun empty => nomatch empty)

def frameArena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := LinearIndependent F₂ (observation.readout () ())

theorem frame_source_bridge :
    (type_of% (@frame_independent)) ↔ frameArena.Law frameActual := Iff.rfl

private theorem frame_rejected : ¬ frameArena.Law rejected := by
  intro law
  exact law.ne_zero (Sum.inl (0 : Fin 12)) rfl

private theorem frame_dependence : ObservationalDependence signature frameActual := by
  intro role
  refine ⟨(), Sum.inl (0 : Fin 12), Sum.inr (0 : Fin 12), ?_⟩
  change frame (Sum.inl (0 : Fin 12)) ≠ frame (Sum.inr (0 : Fin 12))
  simpa only [← hyperbolic_basis_apply] using hyperbolicBasis.injective.ne
    (by simp : Sum.inl (0 : Fin 12) ≠ Sum.inr (0 : Fin 12))

def frameFamilyRegistration : Registration frameArena (type_of% (@frame_independent)) where
  actual := frameActual
  bridge := frame_source_bridge
  variation := ⟨frame_source_bridge.mp frame_independent, rejected, frame_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    frameArena.Law frameActual rejected frame_rejected
  dependence := frame_dependence

def frameRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@frame_independent)
    (type_of% (realize signature frameActual.readout frameActual.anchor)) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic.frame_independent "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic.frameFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨frameArena⟩
  objectArena := .source ⟨frameArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source frameArena ⟨frameFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature frameActual.readout frameActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms familyRegistration
#print axioms frameFamilyRegistration

end

end Reg.D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic
