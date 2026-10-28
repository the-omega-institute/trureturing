import D5.S3.VertexAlgebra.TwistedGround.FlipAverage
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact source equivalence and variation for the flip-average trace. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FlipAverage

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
open _root_.D5.S3.VertexAlgebra.TwistedGround.FlipAverage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
attribute [local instance] _root_.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.reducedFintype
  _root_.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.quotientFintype
  _root_.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.cardInvertible

abbrev Parameters := {D : LatticeData // IsUnit D.G.det}
abbrev Reps (p : Parameters) :=
  Representation ℂ (Extension p.1 ⧸ K p.1) (ActualGround p.1 p.2)
abbrev EndForms (p : Parameters) :=
  Module.End ℂ (LinearMap.BilinForm ℂ (ActualGround p.1 p.2))

abbrev signature := Reg.Support.SingleDependentReadout.signature Parameters Reps EndForms

def actual : Realization signature :=
  realize signature (fun _ _ rho => (Representation.linHom rho rho.dual).averageMap)
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det),
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ (ActualGround D hu))
      (LinearMap.BilinForm.flipHom.toLinearMap.comp
        (observation.readout () ⟨D, hu⟩ (groundRepresentation D hu))) = 1

theorem exact_source_bridge :
    (type_of% (@actual_flip_average_trace)) ↔ arena.Law actual := by
  rfl

private def plane : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric i j := by fin_cases i <;> fin_cases j <;> rfl
  even_diagonal i := by fin_cases i <;> exact ⟨0, rfl⟩

private theorem plane_unit : IsUnit plane.G.det := by
  change IsUnit ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det)
  norm_num [Matrix.det_fin_two]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law plane plane_unit
  change LinearMap.trace ℂ _ (LinearMap.BilinForm.flipHom.toLinearMap.comp 0) = 1 at h
  simp at h

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨plane, plane_unit⟩, groundRepresentation plane plane_unit,
    Representation.trivial ℂ (Extension plane ⧸ K plane) (ActualGround plane plane_unit), ?_⟩
  change (Representation.linHom (groundRepresentation plane plane_unit)
    (groundRepresentation plane plane_unit).dual).averageMap ≠
    (Representation.linHom
      (Representation.trivial ℂ (Extension plane ⧸ K plane) (ActualGround plane plane_unit))
      (Representation.trivial ℂ (Extension plane ⧸ K plane)
        (ActualGround plane plane_unit)).dual).averageMap
  intro h
  have ht := _root_.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.average_trace
    plane plane_unit
  change LinearMap.trace ℂ _ ((Representation.linHom (groundRepresentation plane plane_unit)
    (groundRepresentation plane plane_unit).dual).averageMap) = 1 at ht
  rw [h] at ht
  have trivial_average : (Representation.linHom
      (Representation.trivial ℂ (Extension plane ⧸ K plane) (ActualGround plane plane_unit))
      (Representation.trivial ℂ (Extension plane ⧸ K plane)
        (ActualGround plane plane_unit)).dual).averageMap = 1 := by
    apply LinearMap.ext
    intro B
    apply Representation.averageMap_id
    intro g
    ext u v
    simp [Representation.linHom, Representation.dual, Representation.trivial]
  rw [trivial_average, LinearMap.trace_one] at ht
  simp only [Module.finrank_linearMap, Module.finrank_linearMap_self] at ht
  rw [actual_ground_finrank] at ht
  norm_num [plane] at ht

def familyRegistration : Registration arena (type_of% (@actual_flip_average_trace)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp (@actual_flip_average_trace), rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_flip_average_trace)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.FlipAverage.actual_flip_average_trace "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FlipAverage.familyRegistration
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms exact_source_bridge
#print axioms familyRegistration
end
end Reg.D5.S3.VertexAlgebra.TwistedGround.FlipAverage
