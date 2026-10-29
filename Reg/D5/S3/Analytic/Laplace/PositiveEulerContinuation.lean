import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.PositiveEulerContinuation
import Reg.Support.SingleDependentReadout

/-! The complete original law is retained. The analyticity readout acts on
complex functions, with zero and the reciprocal giving distinct observations. -/

noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Complex
open _root_.D5.S3.Analytic.Laplace.PositiveEulerContinuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Laplace.PositiveEulerContinuation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ) (fun _ => Set ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ F s => AnalyticOnNhd ℂ F s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law Q := ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    [IsFiniteMeasure μ],
    AEMeasurable X μ → (∀ᵐ ω ∂μ, 0 ≤ X ω) →
    ∀ {a : ℝ}, a < 0 → ∀ {R : ℂ → ℂ},
    MeromorphicOn R {z | a < z.re} →
    (∀ x : ℝ, a < x → AnalyticAt ℂ R (x : ℂ)) →
    (∀ z : ℂ, 0 < z.re →
      z * deriv (deriv (fun w => complexMGF X μ (-w))) z +
        2 * deriv (fun w => complexMGF X μ (-w)) z = R z) →
    (∀ x : ℝ, a < x → Integrable (fun ω => Real.exp (-x * X ω)) μ) ∧
      Q.readout () () (fun z => complexMGF X μ (-z)) {z | a < z.re}

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (Ω := ULift.{u} ℕ) (μ := 0) (X := fun _ => 0)
    (by fun_prop) (by simp) (a := -1) (by norm_num) (R := fun _ => 0)
    (fun z _ => analyticAt_const.meromorphicAt)
    (fun _ _ => analyticAt_const)
    (by intro z hz; simp [complexMGF])
  exact hh.2

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℂ => 0), (fun z : ℂ => z⁻¹), ?_⟩
  intro he
  have he' : AnalyticOnNhd ℂ (fun _ : ℂ => 0) univ =
      AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) univ := congrFun he univ
  have hi : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) univ := by
    rw [← he']
    exact analyticOnNhd_const
  exact (differentiableAt_inv_iff.mp (hi 0 (mem_univ 0)).differentiableAt) rfl

def evidence : Registration arena.{u} (type_of% @integrable_and_analytic_of_euler.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integrable_and_analytic_of_euler.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integrable_and_analytic_of_euler.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.PositiveEulerContinuation.integrable_and_analytic_of_euler.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.PositiveEulerContinuation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F s => AnalyticOnNhd ℂ F s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.PositiveEulerContinuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Laplace.PositiveEulerContinuation
