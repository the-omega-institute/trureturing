import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockChargedSeedPhysical

/-! Faithful dependent-family audit of the charged-seed coefficient law. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedSeedPhysical

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedSeedPhysical
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators TensorProduct

noncomputable section

private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro first second; fin_cases first <;> fin_cases second <;> rfl
  even_diagonal := by intro axis; fin_cases axis <;> exact ⟨0, rfl⟩

private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have determinant : hyperbolic.G.det = -1 := by
    change (Matrix.det (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)) = -1
    norm_num [Matrix.det_fin_two]
  rw [determinant]
  exact isUnit_neg_one

private def probeGround : ActualGround hyperbolic hyperbolic_unit := fun _ => 1

private theorem probeGround_nonzero : probeGround ≠ 0 := by
  intro equality
  have coordinate := congrFun equality (0 : Half (groundRank hyperbolic hyperbolic_unit))
  exact one_ne_zero (show (1 : ℂ) = 0 from coordinate)

private def probeState : ActualTensor hyperbolic hyperbolic_unit :=
  (1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeGround

private theorem probe_leading :
    chargedCoefficient hyperbolic hyperbolic_unit 0 0 probeState ≠ 0 := by
  simpa [probeState, chargeNorm, bilinear] using
    charged_ground_leading hyperbolic hyperbolic_unit 0 probeGround probeGround_nonzero

private theorem probeState_nonzero : probeState ≠ 0 := by
  intro zero
  apply probe_leading
  rw [zero, map_zero]

abbrev BoundData := { lattice : LatticeData // IsUnit lattice.G.det }
abbrev Parameter := Σ data : BoundData, Charge data.val × ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun p => ActualTensor p.1.val p.1.property)
  (fun p => ActualTensor p.1.val p.1.property)

def actual : Realization signature := realize signature
  (fun _ p vector => chargedCoefficient p.1.val p.1.property p.2.1 (p.2.2 + 2) vector)
  (fun empty => nomatch empty)

/-- Identity replacement, rather than the homogeneous all-zero readout. -/
def rejected : Realization signature := realize signature
  (fun _ _ vector => vector) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (e : ℤ) (v : ActualTensor D hu),
    (∑ colour : Fin D.rank, (charge colour : ℂ) •
      (wordField D hu (chargedField D hu charge) [(colour, 0)]).coeff e v) -
        ((chargeNorm D charge : ℂ) / 2) •
          readout.readout () ⟨⟨D, hu⟩, charge, e⟩ v =
      (((e + 2 : ℤ) : ℂ) / 2) •
        readout.readout () ⟨⟨D, hu⟩, charge, e⟩ v

theorem source_bridge :
    (type_of% (@charged_seed_physical_coefficient)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit 0 0 probeState
  exact probeState_nonzero (by
    simpa [rejected, realize, chargeNorm, bilinear] using bad.symm)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨⟨hyperbolic, hyperbolic_unit⟩, 0, -2⟩, 0, probeState, ?_⟩
  intro equality
  change chargedCoefficient hyperbolic hyperbolic_unit 0 0 0 =
    chargedCoefficient hyperbolic hyperbolic_unit 0 0 probeState at equality
  exact probe_leading (by simpa only [map_zero] using equality.symm)

def familyRegistration :
    Registration arena (type_of% (@charged_seed_physical_coefficient)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp charged_seed_physical_coefficient, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_seed_physical_coefficient)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedSeedPhysical.charged_seed_physical_coefficient
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedSeedPhysical.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedSeedPhysical
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedSeedPhysical
