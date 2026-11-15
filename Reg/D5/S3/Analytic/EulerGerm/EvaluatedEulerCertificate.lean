import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.EulerGerm.EvaluatedEulerCertificate
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.EulerGerm.EvaluatedEulerCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.EulerGerm.EvaluatedEulerCertificate

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ C => C) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Observe the nonnegative constant without changing any other part of the telescope. -/
def arena : Arena where
  signature := signature
  Law Q := ∀ {J I T : Type} [Fintype J] [Fintype I] [Fintype T]
    (d : Data J I T) (N : ℕ) (hcert : d.Certificate)
    (hmode : ∀ i, 1 ≤ ∑ j, d.mode i j)
    (htail : ∀ t, N + 1 ≤ ∑ j, d.tailMode t j)
    (b : J → ℝ) (m ε A : ℝ) (hm : 0 < m) (hb : ∀ j, m ≤ b j)
    (hε : 0 < ε) (hA : 0 ≤ A) (hcut : 2 ≤ (N + 1 : ℝ) * ε * m),
    ∃ C : ℝ, 0 ≤ Q.readout () () C ∧ ∀ R : Nat.Primes → ℂ → ℂ,
      (∀ p, AnalyticOnNhd ℂ (R p) {s : ℂ | ε < s.re}) →
      (∀ p s, ε < s.re → ‖R p s‖ ≤ A / (p : ℝ) ^ 2) →
      ∀ p, AnalyticOnNhd ℂ (d.corrected b R p) {s : ℂ | ε < s.re} ∧
        ∀ s, ε < s.re → ‖d.corrected b R p s - 1‖ ≤ C / (p : ℝ) ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let d : Data PEmpty PEmpty PEmpty := {
    linear := fun j => nomatch j
    mode := fun i => nomatch i
    power := fun i => nomatch i
    tailMode := fun t => nomatch t
    tailCoeff := fun t => nomatch t }
  have hc : d.Certificate := by
    intro z
    simp [Data.numerator, Data.denominator, Data.tail]
  obtain ⟨C, hC, _⟩ := h d 0 hc (fun i => nomatch i) (fun t => nomatch t)
    (fun j => nomatch j) 1 2 0 (by norm_num) (fun j => nomatch j)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hC

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩

def family : Registration arena (type_of% (@evaluated_certificate_uniform)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@evaluated_certificate_uniform, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@evaluated_certificate_uniform) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.EulerGerm.EvaluatedEulerCertificate.evaluated_certificate_uniform.audit
  realizationName := `Reg.D5.S3.Analytic.EulerGerm.EvaluatedEulerCertificate.family
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
    owner := `D5.S3.Analytic.EulerGerm.EvaluatedEulerCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 20
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Analytic.EulerGerm.EvaluatedEulerCertificate
