import D5.S3.VertexAlgebra.TwistedGround.SymmetricPairing
import Reg.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing

/-! Exact source equivalence and variation for the selected symmetric pairing. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.SymmetricPairing

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.TwistedGround.SymmetricPairing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
open scoped BigOperators


abbrev signature := Reg.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.signature
abbrev actual := Reg.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.actual

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det),
    ∃ B : LinearMap.BilinForm ℂ (ActualGround D hu), B.Nondegenerate ∧ B.IsSymm ∧
      (∀ (g : Extension D ⧸ K D) (u v : ActualGround D hu),
        B (observation.readout () ⟨D, hu⟩ (groundRepresentation D hu) g u)
          (observation.readout () ⟨D, hu⟩ (groundRepresentation D hu) g v) = B u v) ∧
      (∀ (a : Charge D) (u v : ActualGround D hu),
        B (observation.readout () ⟨D, hu⟩ (groundRepresentation D hu) (groundLift D a) u) v =
          paritySign (bilinear D a a / 2) *
            B u (observation.readout () ⟨D, hu⟩ (groundRepresentation D hu) (groundLift D a) v))

theorem exact_source_bridge :
    (type_of% (@actual_symmetric_ground_pairing)) ↔ arena.Law actual := by
  constructor
  · intro source D hu
    obtain ⟨B⟩ := source D hu
    exact ⟨B.form, B.nondegenerate, B.symmetric, B.invariant, B.signed_adjoint⟩
  · intro law D hu
    obtain ⟨B, nondegenerate, symmetric, invariant, adjoint⟩ := law D hu
    exact ⟨{
      form := B
      nondegenerate := nondegenerate
      invariant := invariant
      signed_adjoint := adjoint
      symmetric := symmetric }⟩

private theorem forget_symmetric (observation : Realization signature)
    (h : arena.Law observation) :
    Reg.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.arena.Law observation := by
  intro D hu
  obtain ⟨B, hn, _, hi, ha⟩ := h D hu
  exact ⟨B, hn, hi, ha⟩

private def bad : Realization signature :=
  Classical.choose
    Reg.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.familyRegistration.variation.2

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  exact Classical.choose_spec
    Reg.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.familyRegistration.variation.2
    (forget_symmetric bad h)

def familyRegistration : Registration arena (type_of% (@actual_symmetric_ground_pairing)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp (@actual_symmetric_ground_pairing), bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad bad_law
  dependence := Reg.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.familyRegistration.dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_symmetric_ground_pairing)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := Lean.Name.str
    (Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.SymmetricPairing
      "actual_symmetric_ground_pairing") "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SymmetricPairing.familyRegistration
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
end Reg.D5.S3.VertexAlgebra.TwistedGround.SymmetricPairing
