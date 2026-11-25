import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.MonotoneTailSharpness
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.MonotoneTailSharpness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MonotoneTailSharpness

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ s => s ^ 3) (fun e => nomatch e)

def negativeBudget : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V :=
    ∀ {s : ℝ}, 0 < s → s ≤ 1 / 2 →
      ∃ A : ℝ → ℝ, Monotone A ∧ (∀ t ≥ 1, 0 ≤ A t) ∧
        (∀ t ∉ Icc (2 - s) (2 + s), A t = t) ∧
        Integrable (fun t => (A t - t) / t ^ 2) ∧
        let Q := fun z => ∫ t in Ioi z, (A t - t) / t ^ 2
        Q 2 = -s ^ 2 / 32 ∧
          (∫ z in (1 : ℝ)..3, max (-Q z) 0 / Real.sqrt z) ≤ V.readout () () s / 16

private theorem negativeBudget_fails : ¬ arena.Law negativeBudget := by
  intro h
  obtain ⟨A, -, -, -, -, -, hbound⟩ := h (s := 1 / 2) (by norm_num) le_rfl
  change (∫ z in (1 : ℝ)..3,
    max (-(∫ t in Ioi z, (A t - t) / t ^ 2)) 0 / Real.sqrt z) ≤ (-1 : ℝ) / 16 at hbound
  have hnonneg : 0 ≤ ∫ z in (1 : ℝ)..3,
      max (-(∫ t in Ioi z, (A t - t) / t ^ 2)) 0 / Real.sqrt z := by
    apply intervalIntegral.integral_nonneg_of_forall (by norm_num)
    intro z
    exact div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  change (0 : ℝ) ^ 3 ≠ (1 : ℝ) ^ 3
  norm_num

def family : Registration arena (type_of% @monotone_tail_quadratic_depth_cubic_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@monotone_tail_quadratic_depth_cubic_mass, negativeBudget, negativeBudget_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual negativeBudget negativeBudget_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@monotone_tail_quadratic_depth_cubic_mass) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.MonotoneTailSharpness.monotone_tail_quadratic_depth_cubic_mass
    "__information_unit"
  realizationName := .str `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MonotoneTailSharpness "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s ^ 3) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.MonotoneTailSharpness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg", "arg",
        "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MonotoneTailSharpness
