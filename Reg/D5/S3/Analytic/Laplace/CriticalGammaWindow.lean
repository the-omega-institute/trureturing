import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.CriticalGammaWindow
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Real Set Filter
open _root_.D5.S3.Analytic.Laplace.CriticalGammaWindow
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Laplace.CriticalGammaWindow

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

/-- The decay readout on the integer moment orders. -/
def actual : Realization signature :=
  realize signature (fun _ _ k => (512 : ℝ)⁻¹ ^ k) (fun e => nomatch e)

def negativeScale : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {a : ℝ} (ha : 1 ≤ a) {g : ℝ → ℝ} (hg : Measurable g)
    {M : ℝ} (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2*u)),
    let k := ⌊640*a⌋₊
    let f := fun u : ℝ => |g u| * (u ^ k * exp (-(512*u)) / k.factorial)
    let S := Ioi (0:ℝ) \ Icc a (3*a/2)
    a ≤ (k:ℝ) ∧ IntegrableOn f S ∧
      (∫ u in S, f u) ≤ M * (1/542 + 1/478) * V.readout () () k

private theorem negative_fails : ¬ arena.Law negativeScale := by
  intro h
  have h0 : ∀ u : ℝ, 0 ≤ u → |(fun _ : ℝ => (0 : ℝ)) u| ≤ 1 * exp (2*u) := by
    intro u _
    simpa only [abs_zero, one_mul] using (Real.exp_pos (2*u)).le
  have hs := (h (a := 1) le_rfl (g := fun _ : ℝ => (0 : ℝ)) measurable_const (M := 1) h0).2.2
  change ((∫ u in _, |(0 : ℝ)| * _) : ℝ) ≤ 1 * (1 / 542 + 1 / 478) * (-1) at hs
  norm_num at hs

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (0:ℕ), (1:ℕ), ?_⟩
  change (512 : ℝ)⁻¹ ^ 0 ≠ (512 : ℝ)⁻¹ ^ 1
  norm_num

def family : Registration arena (type_of% @critical_window_off_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@critical_window_off_mass, negativeScale, negative_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual negativeScale negative_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@critical_window_off_mass) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Analytic.Laplace.CriticalGammaWindow.critical_window_off_mass
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Analytic.Laplace.CriticalGammaWindow "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ k => (512 : ℝ)⁻¹ ^ k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.CriticalGammaWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Laplace.CriticalGammaWindow
