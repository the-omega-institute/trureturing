import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.ThetaIntegratedReflectionGap
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaGamma.ThetaReflectedKernelComparison
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Weil.ZetaGamma.ThetaIntegratedReflectionGap

/-- Keep the complete source telescope; observe the positive physical entry. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ((_ : ℝ) × ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p b => physicalKernel p.2 p.1 b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {a b v : ℝ}, 0 < a → 0 < b →
    0 < reflectedRadialMoment v a b ∧
      (a * b / 24) * reflectedRadialMoment v a b <
        R.readout () ⟨a, v⟩ b - physicalKernel v a (-b)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (a := 1) (b := 1) (v := 0) (by norm_num) (by norm_num)
  have hp := (physical_kernel_reflection_comparison
    (a := 1) (b := 1) (v := 0) (by norm_num) (by norm_num) le_rfl).1
  have hn : (1 * 1 / 24 : ℝ) * reflectedRadialMoment 0 1 1 <
      0 - physicalKernel 0 1 (-1) := hh.2
  nlinarith [hh.1, hp]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, -1, 1, ?_⟩
  exact ne_of_lt (physical_kernel_reflection_comparison
    (a := 1) (b := 1) (v := 0) (by norm_num) (by norm_num) le_rfl).2

def evidence : Registration arena (type_of% @physical_kernel_integrated_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_kernel_integrated_gap, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@physical_kernel_integrated_gap) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.ThetaIntegratedReflectionGap.integratedGapUnit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.ThetaIntegratedReflectionGap.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p b => physicalKernel p.2 p.1 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.ThetaIntegratedReflectionGap
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaGamma.ThetaIntegratedReflectionGap
