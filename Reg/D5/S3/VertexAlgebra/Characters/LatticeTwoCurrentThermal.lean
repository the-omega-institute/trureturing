import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentTrace
import D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentThermal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeTwoCurrentTrace
open LatticeTwoCurrentThermal

open private probe probePositive cutoff_zero multiplicity_zero
  from Reg.D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentTrace

namespace Reg.D5.S3.VertexAlgebra.LatticeTwoCurrentThermal

structure Params where
  D : LatticeData
  positive : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  i : Fin D.rank
  j : Fin D.rank
  q1 : ℂ
  q2 : ℂ
  disk1 : ‖q1‖ < 1
  disk2 : ‖q2‖ < 1

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun _ => ℕ × ℕ) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p nm => p.q1^nm.1*p.q2^nm.2*
    actualCurrentCycleTrace p.D p.positive p.i p.j nm.1 nm.2)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (q1 q2 : ℂ) (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1),
    Summable (fun nm : ℕ × ℕ => ‖a.readout () ⟨D,hD,i,j,q1,q2,hq1,hq2⟩ nm‖) ∧
    HasSum (fun nm : ℕ × ℕ => a.readout () ⟨D,hD,i,j,q1,q2,hq1,hq2⟩ nm)
      (oscillatorCharacter D (q1*q2) *
        (chargeMoment D i j (q1*q2) + (D.G i j : ℂ)*chargeTheta D (q1*q2)*
          ∑' k : ℕ, (k+1 : ℂ)*(q1^(k+1)+q2^(k+1))/(1-(q1*q2)^(k+1))))

private theorem bridge : (type_of% (@ordinary_two_current_thermal)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := (h probe probePositive 0 0 0 0 (by norm_num) (by norm_num)).1
  change Summable (fun _ : ℕ × ℕ => ‖(1:ℂ)‖) at hs
  simpa only [norm_one, summable_const_iff, one_ne_zero] using hs

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probe,probePositive,0,0,0,1/2,by norm_num,by norm_num⟩,(0,0),(0,1),?_⟩
  change (0:ℂ)^0*(1/2:ℂ)^0*actualCurrentCycleTrace probe probePositive 0 0 0 0 ≠
    (0:ℂ)^0*(1/2:ℂ)^1*actualCurrentCycleTrace probe probePositive 0 0 0 1
  rw [actual_two_current_grade_trace, actual_two_current_grade_trace]
  norm_num [cutoff_zero, multiplicity_zero, bilinear, probe, chargeEnergy, Nat.dist,
    LatticePositiveEnergy.chargeEnergy_zero]

def family : Registration arena (type_of% (@ordinary_two_current_thermal)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp ordinary_two_current_thermal, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ordinary_two_current_thermal) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeTwoCurrentThermal.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeTwoCurrentThermal.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentThermal
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg","fn","arg","body","arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","body","body","arg","fn","fn","arg","body"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.VertexAlgebra.LatticeTwoCurrentThermal
