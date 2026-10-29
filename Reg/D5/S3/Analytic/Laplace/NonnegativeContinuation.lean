import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.NonnegativeContinuation
import Reg.Support.DependentFamily

open _root_.D5.S3.Analytic.Laplace.NonnegativeContinuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace Reg.D5.S3.Analytic.Laplace.NonnegativeContinuation
noncomputable section
universe u

abbrev signature : Signature where
  Params := ℂ → ℂ
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ H z => H z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Every original type, measure, function, radius and germ hypothesis is retained.
The observation is precisely the extension value in the conclusion. -/
def arena : Arena where
  signature := signature
  Law Q := ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {a R t : ℝ} {H : ℂ → ℂ},
    (∀ᵐ ω ∂μ, 0 ≤ X ω) →
    -a ∈ interior (integrableExpSet X μ) →
    DifferentiableOn ℂ H (Metric.ball (a : ℂ) R) →
    (H =ᶠ[𝓝 (a : ℂ)] fun z => complexMGF X μ (-z)) →
    0 < t → t < R →
    Integrable (fun ω => Real.exp ((t - a) * X ω)) μ ∧
      Q.readout () H ((a - t : ℝ) : ℂ) =
        (∫ ω, Real.exp ((t - a) * X ω) ∂μ : ℝ)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h (Ω := ULift.{u} ℝ) (μ := 0) (X := fun _ => 0)
    (a := 0) (R := 1) (t := 1/2) (H := fun _ => 0)
    (by simp) (by simp [integrableExpSet])
    differentiable_const.differentiableOn (by simp [complexMGF]) (by norm_num) (by norm_num)
  simpa [rejected, realize] using he.2

def registration : Registration arena.{u} (type_of% (@integrable_exp_of_laplace_extension.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integrable_exp_of_laplace_extension.{u}, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨id, 0, 1, zero_ne_one⟩

/-- The single observation is the original H(a-t), with H as parameter
and its actual complex argument as the selected state operand. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integrable_exp_of_laplace_extension.{u})
    (type_of% (realize signature
      (fun _ H z => H z) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.NonnegativeContinuation.integrable_exp_of_laplace_extension.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.NonnegativeContinuation.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ H z => H z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.NonnegativeContinuation
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Laplace.NonnegativeContinuation
