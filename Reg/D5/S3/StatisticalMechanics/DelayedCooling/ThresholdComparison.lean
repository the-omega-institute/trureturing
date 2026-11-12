import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.DelayedCooling.ThresholdComparison
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the concrete threshold comparison. -/

open Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.DelayedCooling.Kernel
open _root_.D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder
open _root_.D5.S3.StatisticalMechanics.DelayedCooling.ThresholdComparison

noncomputable section
namespace Reg.D5.S3.StatisticalMechanics.DelayedCooling.ThresholdComparison

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ τ => synchronousDifference τ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 2) (fun e => nomatch e)

def comparisonArena : Arena where
  signature := signature
  Law R := ∀ {τ t w : ℝ} (_ : 0 < τ) (_ : τ ≤ Real.exp (-1))
    (_ : 0 ≤ t) (_ : 0 ≤ w) (u : ℝ → ℝ)
    (_ : IntegrableOn (fun a => responseKernel τ a * u a) (Ioi 0))
    (_ : IntegrableOn (fun a => responseKernel τ (t + a) * u a) (Ioi 0))
    (_ : ∀ a ∈ Ioi (0 : ℝ), -1 ≤ u a ∧ u a ≤ 1)
    (_ : synchronousDifference τ w 0 ≤ ∫ a in Ioi 0, responseKernel τ a * u a),
    R.readout () () τ w t ≤ ∫ a in Ioi 0, responseKernel τ (t + a) * u a

def comparisonFamily : Registration comparisonArena (type_of% (@threshold_comparison)) := by
  have hbad : ¬ comparisonArena.Law rejected := by
    intro h
    have hτ : 0 < Real.exp (-1) := Real.exp_pos _
    have hm := kernel_tail_mass hτ le_rfl (t := 0) (L := 0) (by norm_num)
    simp only [zero_add, relaxation_of_nonpos hτ le_rfl] at hm
    have hi : IntegrableOn (fun a => responseKernel (Real.exp (-1)) a * 1) (Ioi 0) := by
      simpa using hm.1
    have hg : synchronousDifference (Real.exp (-1)) 0 0 ≤
        ∫ a in Ioi 0, responseKernel (Real.exp (-1)) a * 1 := by
      norm_num [synchronousDifference, relaxation_of_nonpos hτ le_rfl, hm.2]
    have hc := h hτ le_rfl (t := 0) (w := 0) le_rfl le_rfl (fun _ => 1)
      hi (by simpa using hi) (fun _ _ => by norm_num) hg
    norm_num [rejected, realize, hm.2] at hc
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@threshold_comparison, rejected, hbad⟩
    sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
      comparisonArena.Law actual rejected hbad
    dependence := by
      intro _
      refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
      change synchronousDifference 1 ≠ synchronousDifference 2
      intro he
      have h := congrFun (congrFun he 0) 2
      have h1 : relaxation 1 2 = -(1 / 2 : ℝ) := by
        rw [relaxation_eq_source_sum (by norm_num) (by norm_num)]
        norm_num [Finset.sum_range_succ]
      have h2 : relaxation 2 2 = -1 := by
        norm_num [relaxation_initial_segment (by norm_num : (0 : ℝ) < 2)
          (by norm_num : (0 : ℝ) ≤ 2) le_rfl]
      simp only [synchronousDifference, add_zero, h1, h2] at h
      norm_num at h }

def comparisonRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@threshold_comparison)
    (type_of% (realize signature (fun _ _ τ => synchronousDifference τ) (fun e => nomatch e)))
    Type Unit where
  unitName := .str
    `D5.S3.StatisticalMechanics.DelayedCooling.ThresholdComparison.threshold_comparison
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.DelayedCooling.ThresholdComparison.comparisonFamily
  realizationSource := none
  generated := false
  arena := .source ⟨comparisonArena⟩
  objectArena := .source ⟨comparisonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source comparisonArena ⟨comparisonFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ τ => synchronousDifference τ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.DelayedCooling.ThresholdComparison
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.StatisticalMechanics.DelayedCooling.ThresholdComparison
end
