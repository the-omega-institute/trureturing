import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockGroundCharacter
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

/-! The actual dependent tensor readout, its source-equivalence bridge and
whole-family audit obligations. The escape-from carrier binding is unfinished. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockGroundCharacter
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockGradedTrace
open LatticeAllStateField
open HalfFock.LatticeHalfFockGroundCharacter Lattice.NormFourPeirceInvolution
open scoped TensorProduct
open private vacuum_coeff from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  a : Charge D
  v : Carrier D
  e : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => ActualTensor p.D p.hu) (fun p => ActualTensor p.D p.hu)

def actual : Realization signature := realize signature
  (fun _ p x => actualGroundInsert p.D p.hu (groundAction p.D p.hu p.a)
    ((correctedField p.D p.hu p.v).coeff p.e x))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (v : Carrier D) (e : ℤ) (x : ActualTensor D hu),
    r.readout () ⟨D, hu, a, v, e⟩ x =
      (correctedField D hu (chi D a v)).coeff e
        (actualGroundInsert D hu (groundAction D hu a) x)

theorem source_bridge :
    (type_of% (@correctedField_ground_character)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := correctedField_ground_character

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem emptyUnit : IsUnit emptyLattice.G.det := by
  change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
  simp

private def probe : ActualTensor emptyLattice emptyUnit :=
  (1 : Oscillator emptyLattice) ⊗ₜ[ℂ] (fun _ => (1 : ℂ))

private theorem probe_nonzero : probe ≠ 0 := by
  let ev : ActualTensor emptyLattice emptyUnit →ₗ[ℂ] ℂ :=
    (TensorProduct.lid ℂ ℂ).toLinearMap.comp
      (TensorProduct.map (MvPolynomial.lcoeff ℂ 0) (LinearMap.proj 0))
  intro h
  have he := congrArg ev h
  have impossible : (1 : ℂ) = 0 := by simpa [ev, probe] using he
  exact one_ne_zero impossible

private theorem ground_zero (D : LatticeData) (hu : IsUnit D.G.det) :
    groundAction D hu 0 = 1 := by
  unfold groundAction groundLift
  change groundRepresentation D hu (QuotientGroup.mk (1 :
    LatticeTwistedGroundRealization.SignQuotient.Extension D)) = 1
  rw [QuotientGroup.mk_one, map_one]

private theorem vacuum_readout (D : LatticeData) (hu : IsUnit D.G.det)
    (x : ActualTensor D hu) : actual.readout () ⟨D, hu, 0, vacuum D, 0⟩ x = x := by
  change actualGroundInsert D hu (groundAction D hu 0)
    ((correctedField D hu (vacuum D)).coeff 0 x) = x
  rw [vacuum_coeff, if_pos rfl, ground_zero]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p t => simp [actualGroundInsert]
  | add x y hx hy => simp only [map_add, hx, hy]

def rejected : Realization signature := realize signature
  (fun _ p x => actual.readout () p x + x) (fun empty => nomatch empty)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h emptyLattice emptyUnit 0 0 0 probe
  change actualGroundInsert _ _ _ ((correctedField _ _ 0).coeff 0 probe) + probe = _ at he
  simp only [map_zero, LinearMap.zero_apply] at he
  exact probe_nonzero (by simpa using he)

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨emptyLattice, emptyUnit, 0, vacuum emptyLattice, 0⟩, probe, 0, ?_⟩
  have hi : i = () := Subsingleton.elim _ _
  subst i
  rw [vacuum_readout, vacuum_readout]
  exact probe_nonzero

def family : Registration arena (type_of% (@correctedField_ground_character)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correctedField_ground_character)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockGroundCharacter.correctedField_ground_character
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockGroundCharacter.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockGroundCharacter
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockGroundCharacter
