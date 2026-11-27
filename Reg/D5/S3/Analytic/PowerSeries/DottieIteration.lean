import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PowerSeries.DottieIteration
import Reg.Support.SingleDependentReadout

/-! The audit of the cosine iteration observes the iterate `cos^[n] x` as a function of the
number of steps `n`, for each real start `x`, in the convergence clause. -/

noncomputable section
open Filter Topology
open _root_.D5.S3.Analytic.PowerSeries.DottieIteration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace Reg.D5.S3.Analytic.PowerSeries.DottieIteration

/-- The start `x` is the parameter, the number of steps `n` the state, the iterate the output. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x n => Real.cos^[n] x) (fun e => nomatch e)

/-- The constant sequence zero. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete statement of `cos_iterate_tendsto` with the iterate in the convergence clause
replaced by the readout. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ (∀ t : ℝ, Real.cos t = t ↔ t = θ) ∧
    ∀ x : ℝ, Tendsto (fun n : ℕ => R.readout () x n) atTop (𝓝 θ) ∧
      (∀ n : ℕ, |Real.cos^[n + 2] x - θ| ≤ Real.sin 1 ^ n * (1 - θ)) ∧
      ((∀ n : ℕ, Real.cos^[n] x ≠ θ) →
        Tendsto (fun n : ℕ => (Real.cos^[n + 1] x - θ) / (Real.cos^[n] x - θ)) atTop
          (𝓝 (-Real.sin θ)))

/-- The zero sequence converges to `0`, which is not a positive number. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨θ, hθ, -, -, h⟩
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 θ) := (h 0).1
  have := tendsto_nhds_unique tendsto_const_nhds h0
  linarith

/-- From the start `0`, the zeroth iterate is `0` and the first is `cos 0 = 1`. -/
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change Real.cos^[0] (0 : ℝ) ≠ Real.cos^[1] 0
  simp

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @cos_iterate_tendsto

def family : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cos_iterate_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    cos_iterate_tendsto (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.PowerSeries.DottieIteration.cos_iterate_tendsto_unit
  realizationName := `Reg.D5.S3.Analytic.PowerSeries.DottieIteration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x n => Real.cos^[n] x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PowerSeries.DottieIteration
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "arg", "body", "fn", "arg", "fn", "fn", "arg",
        "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.PowerSeries.DottieIteration
