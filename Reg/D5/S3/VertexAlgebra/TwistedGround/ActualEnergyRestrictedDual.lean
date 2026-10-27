import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.TwistedGround.ActualEnergyRestrictedDual

set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.ActualEnergyRestrictedDual
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients _root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint _root_.D5.S3.VertexAlgebra.TwistedGround.ActualEnergyRestrictedDual

structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  h : ℤ
  M : ℤ
  N : ℤ
  e : ℤ
  a : Carrier D
  y : ActualTensor D hu

abbrev signature : Signature where
  Params := Params
  State p := ActualTensor p.D p.hu
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => correctedDualCoefficient p.D p.hu p.e x p.y p.a) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (h M N e : ℤ)
    (a : Carrier D), a ∈ grade D h → ∀ (x y : ActualTensor D hu),
    actualTensorL0 D hu x = ((D.rank : ℂ)/16 + (M : ℂ)/2) • x →
    actualTensorL0 D hu y = ((D.rank : ℂ)/16 + (N : ℂ)/2) • y →
    e+2*h ≠ N-M → readout.readout () ⟨D,hu,h,M,N,e,a,y⟩ x = 0

theorem actual_law : arena.Law actual := by
  intro D hu h M N e a ha x y hx hy hne
  exact correctedDualCoefficient_energy_selection D hu h M N e a ha x y hx hy hne

private def emptyLattice : LatticeData where
  rank := 0
  G := 1
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i
private theorem empty_unit : IsUnit emptyLattice.G.det := by
  change IsUnit (Matrix.det (1 : Matrix (Fin 0) (Fin 0) ℤ))
  rw [Matrix.det_one]
  exact isUnit_one

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h emptyLattice empty_unit 0 0 1 0 0 (by simp) 0 0 (by simp) (by simp) (by decide)
  exact one_ne_zero hz

def familyRegistration : Registration arena (type_of% (@correctedDualCoefficient_energy_selection)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := by
    intro role
    let u := (Pi.basisFun ℂ (LatticeTwistedGroundRealization.Half (groundRank emptyLattice empty_unit))) 0
    have hu0 : u ≠ 0 := (Pi.basisFun ℂ _).ne_zero 0
    obtain ⟨x,hx⟩ := correctedDualCoefficient_nonzero_second_ground emptyLattice empty_unit 0 u hu0
    refine ⟨⟨emptyLattice,empty_unit,0,0,1,-chargeNorm emptyLattice 0,
      Finsupp.single 0 (1 : Oscillator emptyLattice), (1 : Oscillator emptyLattice) ⊗ₜ[ℂ] u⟩, x, 0, ?_⟩
    simpa [actual, realize, correctedDualCoefficient] using hx

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correctedDualCoefficient_energy_selection)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.VertexAlgebra.TwistedGround.ActualEnergyRestrictedDual.correctedDualCoefficient_energy_selection.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ActualEnergyRestrictedDual.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.ActualEnergyRestrictedDual
    definition := none
    coordinates := #[0,1,2,3,4,5,6,9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms registration

/- Additional exact source reconstructions. Each remaining public target is
listed explicitly; these are not four-slot registrations. Full-law variation,
sensitivity, dependence and source classification remain audit obligations. -/
namespace RemainingSourceBridges

def fullReadout (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) : Module.Dual ℂ (Carrier D) := correctedDualCoefficient D hu e x y

theorem off_cover : (type_of% (@correctedDualCoefficient_off_energy_cover)) ↔
    ∀ (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) (x y : ActualTensor D hu) (h : ℤ),
    h ∉ coefficientEnergyCover D hu e x y → ∀ a : Carrier D, a ∈ grade D h →
    fullReadout D hu e x y a = 0 := Iff.rfl

def restrictionReadout (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) (h : ℤ) : Module.Dual ℂ (grade D h) :=
  (grade D h).dualRestrict (correctedDualCoefficient D hu e x y)

theorem restriction_zero : (type_of% (@correctedDualCoefficient_restrict_eq_zero)) ↔
    ∀ (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) (x y : ActualTensor D hu) (h : ℤ),
    h ∉ coefficientEnergyCover D hu e x y → restrictionReadout D hu e x y h = 0 := Iff.rfl

def coordinateReadout (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) (h : ℤ) : Module.Dual ℂ (grade D h) := energyCoefficient D hu e x y h

theorem coordinate : (type_of% (@energyCoefficient_coordinate)) ↔
    ∀ (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) (x y : ActualTensor D hu) (h : ℤ),
    coordinateReadout D hu e x y h =
      (grade D h).dualRestrict (correctedDualCoefficient D hu e x y) := Iff.rfl

def realizationReadout (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) : Module.Dual ℂ (Carrier D) :=
  energyDualRealization D (energyCoefficient D hu e x y)

theorem reconstruction : (type_of% (@energyCoefficient_realization)) ↔
    ∀ (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) (x y : ActualTensor D hu),
    realizationReadout D hu e x y = correctedDualCoefficient D hu e x y := Iff.rfl

theorem homogeneous_reversal : (type_of% (@reversed_coefficient_zero_of_lt_difference)) ↔
    ∀ (D : LatticeData) (hu : IsUnit D.G.det) (h M N r : ℤ), 0 ≤ h →
    ∀ (a : Carrier D), a ∈ grade D h → ∀ (x y : ActualTensor D hu),
    actualTensorL0 D hu x = ((D.rank : ℂ)/16+(M : ℂ)/2) • x →
    actualTensorL0 D hu y = ((D.rank : ℂ)/16+(N : ℂ)/2) • y →
    r < M-N → fullReadout D hu (-r) x y a = 0 := Iff.rfl

theorem full_reversal : (type_of% (@reversed_full_coefficient_zero)) ↔
    ∀ (D : LatticeData) (hu : IsUnit D.G.det),
    Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)) → ∀ (x y : ActualTensor D hu) (r : ℤ),
    r < -(maxOddWeight D hu y : ℤ) → fullReadout D hu (-r) x y = 0 := Iff.rfl

def liftReadout (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) : EnergyRestrictedDual D := energyCoefficientBilinear D hu e x y

theorem lift_reversal : (type_of% (@reversed_energy_coefficient_zero)) ↔
    ∀ (D : LatticeData) (hu : IsUnit D.G.det),
    Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)) → ∀ (x y : ActualTensor D hu) (r : ℤ),
    r < -(maxOddWeight D hu y : ℤ) → liftReadout D hu (-r) x y = 0 := Iff.rfl

end RemainingSourceBridges

end Reg.D5.S3.VertexAlgebra.TwistedGround.ActualEnergyRestrictedDual
