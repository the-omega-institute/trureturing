import D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeLiftRigidity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! A source-bound readout of the phase on a fixed charge. -/

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeLiftRigidity

open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.Lattice
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeTwistedGroundRealization.SignQuotient (complexSignEmbedding)
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate (nebeLatticeData)
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeLiftRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped VertexOperator

noncomputable section

private theorem p48q_order_three_lift_exists :
    ∃ (lift : Carrier nebeLatticeData ≃ₗ[ℂ] Carrier nebeLatticeData)
      (phase : Charge nebeLatticeData → ℂˣ),
      (∀ a : Charge nebeLatticeData,
        lift (Finsupp.single a (1 : Oscillator nebeLatticeData)) =
          (phase a : ℂ) • Finsupp.single (p48qG a) (1 : Oscillator nebeLatticeData)) ∧
      (∀ (u v : Carrier nebeLatticeData) (m : ℤ),
        lift (((Y nebeLatticeData u)[[m]]) v) =
          ((Y nebeLatticeData (lift u))[[m]]) (lift v)) ∧
      lift ^ (3 : ℕ) = 1 ∧
      (∀ a : Charge nebeLatticeData, p48qG a = a → phase a = 1) := by
  have hPeriod (a : Charge nebeLatticeData) : p48qG^[3] a = a := by
    change p48qG (p48qG (p48qG a)) = a
    exact p48qG_cube a
  obtain ⟨chi, _, hCyclicMode, _, hCube, _⟩ :=
    CyclicIsometryLift.cyclic_lift nebeLatticeData p48qG p48qG_isometry 3 (by decide) hPeriod
  let lift := CyclicIsometryLift.corrected nebeLatticeData p48qG chi
  let phase (a : Charge nebeLatticeData) : ℂˣ :=
    IsometryLift.phase nebeLatticeData p48qG a *
      complexSignEmbedding.val (Multiplicative.ofAdd (chi a))
  have hGround (a : Charge nebeLatticeData) :
      lift (Finsupp.single a (1 : Oscillator nebeLatticeData)) =
        (phase a : ℂ) • Finsupp.single (p48qG a) (1 : Oscillator nebeLatticeData) :=
    CyclicIsometryLift.corrected_ground_single nebeLatticeData p48qG p48qG_isometry chi a
  have hMode (u v : Carrier nebeLatticeData) (m : ℤ) :
      lift (((Y nebeLatticeData u)[[m]]) v) =
        ((Y nebeLatticeData (lift u))[[m]]) (lift v) :=
    hCyclicMode u m v
  exact ⟨lift, phase, hGround, hMode, hCube,
    p48q_order_three_lift_standard lift phase hGround hMode hCube⟩

private abbrev LatticeCharge := Charge nebeLatticeData

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (LatticeCharge → ℂˣ)
    (fun _ => LatticeCharge) (fun _ => ℂˣ)

def actual : Realization signature :=
  realize signature (fun _ phase a => phase a) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (lift : Carrier nebeLatticeData ≃ₗ[ℂ] Carrier nebeLatticeData)
    (phase : LatticeCharge → ℂˣ),
    (∀ a, lift (Finsupp.single a (1 : Oscillator nebeLatticeData)) =
      (phase a : ℂ) • Finsupp.single (p48qG a) (1 : Oscillator nebeLatticeData)) →
    (∀ (u v : Carrier nebeLatticeData) (m : ℤ),
      lift (((Y nebeLatticeData u)[[m]]) v) =
        ((Y nebeLatticeData (lift u))[[m]]) (lift v)) →
    lift ^ (3 : ℕ) = 1 →
    ∀ a : LatticeCharge, p48qG a = a → R.readout () phase a = 1

private theorem negativeUnit_ne_one : (-1 : ℂˣ) ≠ 1 := by
  intro h
  have hc := congrArg (fun u : ℂˣ => (u : ℂ)) h
  norm_num at hc

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨lift, phase, ground, modes, cube, _⟩ := p48q_order_three_lift_exists
  exact negativeUnit_ne_one (h lift phase ground modes cube 0 (map_zero p48qG))

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  let coordinate : Fin nebeLatticeData.rank := (0 : Fin 48)
  let phase : LatticeCharge → ℂˣ := fun a => if a coordinate = 0 then -1 else 1
  refine ⟨phase, 0, Pi.single coordinate 1, ?_⟩
  change phase 0 ≠ phase (Pi.single coordinate 1)
  simpa [phase] using negativeUnit_ne_one

def family : Registration arena (type_of% p48q_order_three_lift_standard) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨p48q_order_three_lift_standard, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    p48q_order_three_lift_standard (Realization signature) (LatticeCharge → ℂˣ) Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeLiftRigidity.p48q_order_three_lift_standard
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeLiftRigidity.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeLiftRigidity
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeLiftRigidity
