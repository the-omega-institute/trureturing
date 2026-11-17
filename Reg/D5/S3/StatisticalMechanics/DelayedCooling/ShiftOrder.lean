import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder
import Reg.D5.S3.StatisticalMechanics.DelayedCooling.Kernel

/-! Source-bound audit of the real-shift comparison. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.DelayedCooling.Kernel
open _root_.D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder

noncomputable section
namespace Reg.D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder

abbrev signature := _root_.Reg.D5.S3.StatisticalMechanics.DelayedCooling.Kernel.signature

def actual : Realization signature :=
  realize signature (fun _ _ τ => responseKernel τ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def shiftArena : Arena where
  signature := signature
  Law R := ∀ {τ a b t : ℝ} (_ : 0 < τ) (_ : τ ≤ Real.exp (-1))
    (_ : a ≤ b) (_ : 0 ≤ t),
    responseKernel τ (t + b) * responseKernel τ a ≤
      responseKernel τ (t + a) * R.readout () () τ b

def shiftFamily : Registration shiftArena (type_of% (@kernel_shift_order)) := by
  have hbad : ¬ shiftArena.Law rejected := by
    intro h
    have hcase := h (a := 0) (b := 0) (t := 0)
      (Real.exp_pos (-1)) le_rfl le_rfl le_rfl
    have hz : responseKernel (Real.exp (-1)) 0 = 1 :=
      relaxation_of_nonpos (Real.exp_pos _) (by simpa using (Real.exp_pos (-1)).le)
    norm_num [hz, rejected, realize] at hcase
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@kernel_shift_order, rejected, hbad⟩
    sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
      shiftArena.Law actual rejected hbad
    dependence := by
      intro _
      refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
      change responseKernel 1 ≠ responseKernel 2
      intro he
      have h := congrFun he 2
      have h1 : responseKernel 1 2 = 0 := by
        norm_num [responseKernel, relaxation_initial_segment (by norm_num : (0 : ℝ) < 1)
          (by norm_num : (0 : ℝ) ≤ 1) le_rfl]
      have h2 : responseKernel 2 2 = 1 := by
        norm_num [responseKernel, relaxation_of_nonpos (by norm_num : (0 : ℝ) < 2) le_rfl]
      rw [h1, h2] at h
      norm_num at h }

def shiftRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernel_shift_order)
    (type_of% (realize signature (fun _ _ τ => responseKernel τ) (fun e => nomatch e)))
    Type Unit where
  unitName :=
    `D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder.kernel_shift_order.__information_unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder.shiftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨shiftArena⟩
  objectArena := .source ⟨shiftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shiftArena ⟨shiftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ τ => responseKernel τ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder
end
