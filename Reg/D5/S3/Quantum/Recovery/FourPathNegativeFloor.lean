import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FourPathNegativeFloor
import Reg.Support.SingleDependentReadout

/-! Source-bound registration for the original negative full-triangle lower bound. -/
namespace Reg.D5.S3.Quantum.Recovery.FourPathNegativeFloor
open _root_.D5.S3.Quantum.Recovery.FourPathNegativeFloor
open _root_.D5.S3.Quantum.Recovery.FourPathTriangleFibre
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℝ × ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p Y => G p.1 p.2 Y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ (q X Y : ℝ), 11/100 ≤ q → q ≤ 23/200 →
    0 ≤ X → X ≤ 1 → 0 ≤ Y → Y ≤ 1 →
    19/16+q/2 ≤ Real.sqrt X+Real.sqrt Y → (23:ℝ)/50 < A.readout () (q,X) Y

theorem rejected_law : ¬ arena.Law rejected := by
  intro hv
  have hv' := hv (11/100) 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected,realize] at hv'

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(1,1),0,1,?_⟩
  change G 1 1 0 ≠ G 1 1 1
  have hp : 0 < h := by unfold h; positivity
  have left : G 1 1 0=E 1-4*h^2 := by
    simp [G,Gamma,C,F,Real.sq_sqrt (sq_nonneg h)]
  have right : G 1 1 1=E 1 := by simp [G,Gamma,C,F]
  rw [left,right]
  nlinarith only [sq_pos_of_pos hp]

def source_registration : Registration arena
    (∀ (q X Y : ℝ), 11/100 ≤ q → q ≤ 23/200 →
      0 ≤ X → X ≤ 1 → 0 ≤ Y → Y ≤ 1 →
      19/16+q/2 ≤ Real.sqrt X+Real.sqrt Y → (23:ℝ)/50 < G q X Y) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨negative_floor,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Recovery.FourPathNegativeFloor.negative_floor)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathNegativeFloor.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathNegativeFloor.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p Y => G p.1 p.2 Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.FourPathNegativeFloor
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end
end Reg.D5.S3.Quantum.Recovery.FourPathNegativeFloor
