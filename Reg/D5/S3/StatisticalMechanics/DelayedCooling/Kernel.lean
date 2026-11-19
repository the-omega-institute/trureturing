import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.DelayedCooling.Kernel
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of positivity of the concrete relaxation. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.DelayedCooling.Kernel

noncomputable section
namespace Reg.D5.S3.StatisticalMechanics.DelayedCooling.Kernel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ τ => relaxation τ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def positivityArena : Arena where
  signature := signature
  Law R := ∀ {τ : ℝ} (_ : 0 < τ) (_ : τ ≤ Real.exp (-1)) (t : ℝ),
    0 < R.readout () () τ t

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
  change relaxation 1 ≠ relaxation 2
  intro he
  have h := congrFun he 2
  have h1 : relaxation 1 2 = -(1 / 2 : ℝ) := by
    rw [relaxation_eq_source_sum (by norm_num) (by norm_num)]
    norm_num [Finset.sum_range_succ]
  have h2 : relaxation 2 2 = -1 := by
    norm_num [relaxation_initial_segment (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) ≤ 2) le_rfl]
  rw [h1, h2] at h
  norm_num at h

def positivityFamily : Registration positivityArena (type_of% (@relaxation_pos)) := by
  have hbad : ¬ positivityArena.Law rejected := by
    intro h
    have hcase := h (Real.exp_pos (-1)) le_rfl 0
    norm_num [rejected, realize] at hcase
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@relaxation_pos, rejected, hbad⟩
    sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
      positivityArena.Law actual rejected hbad
    dependence := dependence }

def positivityRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@relaxation_pos)
    (type_of% (realize signature (fun _ _ τ => relaxation τ) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.StatisticalMechanics.DelayedCooling.Kernel.relaxation_pos.__information_unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.DelayedCooling.Kernel.positivityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨positivityArena⟩
  objectArena := .source ⟨positivityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source positivityArena ⟨positivityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ τ => relaxation τ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.DelayedCooling.Kernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.StatisticalMechanics.DelayedCooling.Kernel
end
