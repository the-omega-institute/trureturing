import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.EulerGerm.FiniteIntegerEulerCancellation
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.EulerGerm.FiniteIntegerEulerCancellation
open _root_.D5.S3.Analytic.EulerGerm.EvaluatedEulerCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.EulerGerm.FiniteIntegerEulerCancellation

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ C => C) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Observe the constant in the complete algebraic and analytic telescope. -/
def arena : Arena where
  signature := signature
  Law Q := ∀ {J : Type} [Fintype J] (a : J → ℤ) (N : ℕ),
    ∃ c : FunctionMode J N → ℤ,
      (∀ u : J → ℕ, (∑ j, u j) ≤ N →
        (residual a (polynomialMode N) c).coeff (Finsupp.equivFunOnFinite.symm u) = 0) ∧
      (tailData a (polynomialMode N) c).Certificate ∧
      (∀ i, 1 ≤ ∑ j, (tailData a (polynomialMode N) c).mode i j ∧
        (∑ j, (tailData a (polynomialMode N) c).mode i j) ≤ N) ∧
      (∀ t, N + 1 ≤ ∑ j, (tailData a (polynomialMode N) c).tailMode t j) ∧
      ∀ (b : J → ℝ) (m ε A : ℝ), 0 < m → (∀ j, m ≤ b j) →
        0 < ε → 0 ≤ A → 2 ≤ (N + 1 : ℝ) * ε * m →
        ∃ C : ℝ, 0 ≤ Q.readout () () C ∧ ∀ R : Nat.Primes → ℂ → ℂ,
          (∀ p, AnalyticOnNhd ℂ (R p) {s : ℂ | ε < s.re}) →
          (∀ p s, ε < s.re → ‖R p s‖ ≤ A / (p : ℝ) ^ 2) →
          ∀ p, AnalyticOnNhd ℂ ((tailData a (polynomialMode N) c).corrected b R p)
              {s : ℂ | ε < s.re} ∧
            ∀ s, ε < s.re →
              ‖(tailData a (polynomialMode N) c).corrected b R p s - 1‖ ≤ C / (p : ℝ) ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, _, _, _, _, ha⟩ := h (J := PEmpty) (fun j => nomatch j) 0
  obtain ⟨C, hC, _⟩ := ha (fun j => nomatch j) 1 2 0 (by norm_num)
    (fun j => nomatch j) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hC

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩

def family : Registration arena (type_of% (@finite_integer_euler_cancellation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_integer_euler_cancellation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_integer_euler_cancellation) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.EulerGerm.FiniteIntegerEulerCancellation.finite_integer_euler_cancellation.audit
  realizationName := `Reg.D5.S3.Analytic.EulerGerm.FiniteIntegerEulerCancellation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ C => C) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.EulerGerm.FiniteIntegerEulerCancellation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Analytic.EulerGerm.FiniteIntegerEulerCancellation
