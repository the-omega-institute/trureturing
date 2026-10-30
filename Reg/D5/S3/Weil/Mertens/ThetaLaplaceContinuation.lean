import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.ThetaLaplaceContinuation
import Reg.Support.SingleDependentReadout

/-! The complete actual continuation law with its physical-integrand observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Weil.Mertens.ThetaLaplaceContinuation

open Set MeasureTheory Filter Complex
open scoped BigOperators Topology
open _root_.D5.S3.Weil.Mertens.ThetaLaplaceContinuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℂ (fun _ => ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ s u => Complex.exp (-s * (u : ℂ)) * (q u : ℂ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Every clause and quantifier of the continuation theorem is retained. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u₀ : ℝ), 0 ≤ u₀ →
    AnalyticOnNhd ℂ C {z | (1 / 2 : ℝ) < z.re} ∧
    Differentiable ℂ (A u₀) ∧
    (∀ z : ℂ, (1 / 2 : ℝ) < z.re →
      LSeriesSummable (fun n => (b n : ℂ)) z ∧
      Summable (fun pj : Nat.Primes × ℕ =>
        ‖(Real.log (pj.1 : ℝ) : ℂ) * (pj.1 : ℂ) ^ (-((pj.2 + 2 : ℕ) : ℂ) * z)‖) ∧
      C z = ∑' p : Nat.Primes, ∑' j : ℕ,
        (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-((j + 2 : ℕ) : ℂ) * z)) ∧
    (∀ s : ℂ, 0 < s.re →
      IntegrableOn (R.readout () s) (Ioi u₀) ∧
      Q u₀ s = M u₀ s ∧
      IntegrableOn (fun u : ℝ => (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ))
        (Ioi u₀) ∧
      HasDerivAt (Q u₀)
        (-(∫ u in Ioi u₀, (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ))) s) ∧
    MeromorphicOn (M u₀) D ∧
    AnalyticAt ℂ (M u₀) 0 ∧
    M u₀ 0 = -1 - (Real.eulerMascheroniConstant : ℂ) - C 1 - A u₀ 0 ∧
    (∀ ρ : ℂ, (1 / 2 : ℝ) < ρ.re → riemannZeta ρ = 0 →
      let a := ρ - 1
      let m := analyticOrderNatAt riemannZeta ρ
      let α := -(m : ℂ) / ρ
      a ∈ D ∧ a ≠ 0 ∧ 0 < m ∧ analyticOrderAt riemannZeta ρ ≠ ⊤ ∧ α ≠ 0 ∧
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧
        M u₀ =ᶠ[𝓝[≠] a] (fun s => α / (s - a) + H s) ∧
        (fun s => -deriv (M u₀) s + M u₀ s) =ᶠ[𝓝[≠] a]
          (fun s => α / (s - a) ^ 2 + α / (s - a) + H s - deriv H s) ∧
        meromorphicOrderAt (M u₀) a = (-1 : ℤ) ∧
        meromorphicOrderAt (fun s => -deriv (M u₀) s + M u₀ s) a = (-2 : ℤ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioi (0 : ℝ)) :=
    ((h 0 (by norm_num)).2.2.2.1 1 (by norm_num)).1
  simpa [integrableOn_const_iff, Real.volume_Ioi] using hi

private lemma readout_log {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    Complex.exp (-(1 : ℂ) * (Real.log x : ℂ)) * (q (Real.log x) : ℂ) =
      -(x : ℂ)⁻¹ := by
  have hq : q (Real.log x) = -1 := by
    rw [q, Real.exp_log hx, Chebyshev.theta_eq_zero_of_lt_two hx2,
      zero_sub, Real.exp_neg, Real.exp_log hx]
    field_simp
  rw [hq]
  simp only [neg_one_mul, Complex.ofReal_neg, Complex.ofReal_one, mul_neg_one]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hx,
    Complex.ofReal_inv]

def family : Registration arena (type_of% (@theta_laplace_continuation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@theta_laplace_continuation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(1 : ℂ), Real.log (4 / 3), Real.log (3 / 2), ?_⟩
    change Complex.exp (-(1 : ℂ) * (Real.log (4 / 3) : ℂ)) *
      (q (Real.log (4 / 3)) : ℂ) ≠
      Complex.exp (-(1 : ℂ) * (Real.log (3 / 2) : ℂ)) * (q (Real.log (3 / 2)) : ℂ)
    rw [readout_log (by norm_num) (by norm_num),
      readout_log (by norm_num) (by norm_num)]
    norm_num

/-- Source selection of the actual integrand in the full continuation law. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@theta_laplace_continuation)
    (type_of% (realize signature actual.readout actual.anchor)) (type_of% ℝ) Unit where
  unitName := `D5.S3.Weil.Mertens.ThetaLaplaceContinuation.theta_laplace_continuation.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.ThetaLaplaceContinuation.family
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
    owner := `D5.S3.Weil.Mertens.ThetaLaplaceContinuation
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "fn", "arg",
        "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end
end Reg.D5.S3.Weil.Mertens.ThetaLaplaceContinuation
