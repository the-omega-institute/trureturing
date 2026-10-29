import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.PositiveEulerContinuation
import Reg.Support.SingleDependentReadout

/-! The complete original law is retained. The observed conjunction joins
actual exponential integrability to analyticity of the actual transform. -/

noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Complex
open _root_.D5.S3.Analytic.Laplace.PositiveEulerContinuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Laplace.PositiveEulerContinuation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ p q => p ∧ q) (fun e => nomatch e)

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
    Q.readout () ()
      (∀ x : ℝ, a < x → Integrable (fun ω => Real.exp (-x * X ω)) μ)
      (AnalyticOnNhd ℂ (fun z => complexMGF X μ (-z)) {z | a < z.re})

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (Ω := ULift.{u} ℕ) (μ := 0) (X := fun _ => 0)
    (by fun_prop) (by simp) (a := -1) (by norm_num) (R := fun _ => 0)
    (fun z _ => analyticAt_const.meromorphicAt)
    (fun _ _ => analyticAt_const)
    (by intro z hz; simp [complexMGF])

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have h := congrFun he True
  simp [actual, realize] at h

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
  readout := some (realize signature (fun _ _ p q => p ∧ q) (fun e => nomatch e))
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
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Laplace.PositiveEulerContinuation
