import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.ActivationTailEuler
import Reg.Support.SingleDependentReadout

noncomputable section
open Real Set MeasureTheory Filter Complex
open scoped Topology
open _root_.D5.S3.Analytic.Laplace.ActivationTailEuler
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Laplace.ActivationTailEuler

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Set ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ F s => IntegrableOn F s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
set_option maxHeartbeats 1000000 in
abbrev arena : Arena where
  signature := signature
  Law V := ∀ {q : ℝ → ℝ} {u₀ : ℝ}, ∀
    (u₀_pos : 0 < u₀) (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)),
    V.readout () () (k q) (Ioi u₀) ∧
    IntegrableOn (f q) (Ioi u₀) ∧
    (∀ u : ℝ, u₀ ≤ u → ‖f q u‖ ≤ ∫ v in Ioi u₀, ‖k q v‖) ∧
    Tendsto (f q) atTop (𝓝 0) ∧
    (∀ a b : ℝ, u₀ ≤ a → a ≤ b → AbsolutelyContinuousOnInterval (f q) a b) ∧
    (∀ᵐ u ∂volume.restrict (Ioi u₀), HasDerivAt (f q) (k q u) u ∧
      u ^ 2 * deriv (f q) u = (u + 1) * q u) ∧
    (∀ U : ℝ, u₀ ≤ U → AnalyticOnNhd ℂ (L q U) {s | 0 < s.re} ∧
      IntegrableOn q (Ioi U) ∧
      ∀ s : ℂ, 0 < s.re →
        (∀ n : ℕ, IntegrableOn (fun u : ℝ =>
          (u : ℂ) ^ n * Complex.exp (-s * (u : ℂ)) * (f q u : ℂ)) (Ioi U)) ∧
        HasDerivAt (L q U)
          (-(∫ u in Ioi U, (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (f q u : ℂ))) s ∧
        HasDerivAt (deriv (L q U))
          (∫ u in Ioi U, (u : ℂ) ^ 2 * Complex.exp (-s * (u : ℂ)) * (f q u : ℂ)) s ∧
        IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (q u : ℂ)) (Ioi U) ∧
        IntegrableOn (fun u : ℝ =>
          (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ)) (Ioi U) ∧
        HasDerivAt (Q q U)
          (-(∫ u in Ioi U, (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ))) s ∧
        s * deriv (deriv (L q U)) s + 2 * deriv (L q U) s =
          -deriv (Q q U) s + Q q U s +
            (U : ℂ) ^ 2 * (f q U : ℂ) * Complex.exp (-s * (U : ℂ)))
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  exact (h (q := fun _ => 0) (u₀ := 1) (by norm_num) measurable_const (by simp)).1
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (1 : ℝ)), ?_⟩
  intro h
  have he := congrFun h (Ioi (1 : ℝ))
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (1 : ℝ)) := by
    change IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi (1 : ℝ)) =
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (1 : ℝ)) at he
    rw [← he]
    simp
  simpa [integrableOn_const_iff, Real.volume_Ioi] using hi
def family : Registration arena (type_of% @actual_tail_laplace_ode) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_tail_laplace_ode, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_tail_laplace_ode) (Realization signature) Type Unit where
  unitName := `D5.S3.Analytic.Laplace.ActivationTailEuler.actual_tail_laplace_ode.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.ActivationTailEuler.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.ActivationTailEuler
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Laplace.ActivationTailEuler
