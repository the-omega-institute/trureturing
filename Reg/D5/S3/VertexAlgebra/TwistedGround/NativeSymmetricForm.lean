import D5.S3.VertexAlgebra.TwistedGround.NativeSymmetricForm
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.NativeSymmetricForm

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice
open _root_.D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic
open _root_.D5.S3.VertexAlgebra.TwistedGround.NativeHyperbolicActions
open _root_.D5.S3.VertexAlgebra.TwistedGround.NativeOrbit
open _root_.D5.S3.VertexAlgebra.TwistedGround
open _root_.D5.S3.VertexAlgebra.TwistedGround.NativeSymmetricForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev Forms := LinearMap.BilinForm ℂ NativeGround

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Forms) (fun _ => Forms)

def actual : Realization signature :=
  realize signature (fun _ _ form => form) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation :=
    observation.readout () () nativePairing ≠ 0 ∧
    (observation.readout () () nativePairing).IsSymm ∧
    (observation.readout () () nativePairing).Nondegenerate ∧
    (∀ element : Extension data ⧸ K data, ∀ first second,
      observation.readout () () nativePairing (nativeRho element first) (nativeRho element second) =
        observation.readout () () nativePairing first second) ∧
    (∀ form : Forms,
      (∀ element : Extension data ⧸ K data, ∀ first second,
        form (nativeRho element first) (nativeRho element second) = form first second) →
      ∃ scalar : ℂ, form = scalar • observation.readout () () nativePairing) ∧
    (∀ charge : Charge data, groundAction data determinantUnit charge ^ 2 =
      complexSign (quadratic data (reduceCharge data charge)) • (1 : Module.End ℂ NativeGround)) ∧
    (Finset.univ.noncommProd (BinaryProjectorProduct.projectorFactor nativeActions)
      (fun first _ second _ _ =>
        BinaryProjectorProduct.factors_commute nativeActions first second) = Pplus) ∧
    (∀ charge : Charge data, ∀ first second,
      observation.readout () () nativePairing (groundAction data determinantUnit charge first)
        second = epsilon data charge (-charge) * observation.readout () () nativePairing first
          (groundAction data determinantUnit (-charge) second))

theorem exact_source_bridge :
    (type_of% (@chosen_native_symmetric_self_duality)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact law.1 rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), nativePairing, 0, ?_⟩
  exact native_pairing_nonzero

def familyRegistration : Registration arena
    (type_of% (@chosen_native_symmetric_self_duality)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp chosen_native_symmetric_self_duality, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chosen_native_symmetric_self_duality)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.NativeSymmetricForm.chosen_native_symmetric_self_duality
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeSymmetricForm.familyRegistration
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

#print axioms familyRegistration

end

end Reg.D5.S3.VertexAlgebra.TwistedGround.NativeSymmetricForm
