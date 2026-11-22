import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory LeanInformationAudit
open scoped Topology
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent (transform)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ => completed) (fun e => nomatch e)

def shifted : Realization signature :=
  realize signature (fun _ _ s => completed s + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V :=
    let F := V.readout () ()
    ((∀ s : ℂ, s ≠ 1 → F s = transform s) ∧
    F 1 = 1 + (Real.eulerMascheroniConstant : ℂ) - deriv (logDeriv riemannZeta₁) 1 ∧
    (∀ s : ℂ, s ≠ 0 → riemannZeta s ≠ 0 → AnalyticAt ℂ F s) ∧
    ∀ G : ℂ → ℂ, ContinuousAt G 1 → (∀ s : ℂ, s ≠ 1 → G s = transform s) → G = F) ∧
    ∀ (p z : ℂ) (r : ℝ), 0 < r → p ≠ z → riemannZeta z = 0 →
      (∀ w ∈ Metric.closedBall p r, w ≠ 0 ∧ (riemannZeta w = 0 → w = z)) →
      let c := (analyticOrderNatAt riemannZeta z : ℂ) / (z * (1-z))
      let J := fun n : ℕ => (p-z)^(n+1) * ((-1 : ℂ)^n / n.factorial) * iteratedDeriv n F p
      ∃ B : ℝ, 0 ≤ B ∧ (∀ n : ℕ,
        ‖iteratedDeriv n F p - c * ((-1 : ℂ)^n * n.factorial *
          (p-z)^(-1-(n : ℤ)))‖ ≤ (n.factorial : ℝ) * B / r^n) ∧
        (∀ n : ℕ, ‖J n - c‖ ≤ B * ‖p-z‖ * (‖p-z‖ / r)^n) ∧
        (‖p-z‖ < r → Tendsto J atTop (𝓝 c) ∧ ∀ᶠ n in atTop, ‖c‖ / 2 ≤ ‖J n‖)

private lemma shifted_fails : ¬ arena.Law shifted := by
  intro h
  have he := h.1.2.1.trans completed_disk_cauchy.1.2.1.symm
  change completed 1 + 1 = completed 1 at he
  exact one_ne_zero (by linear_combination he : (1 : ℂ) = 0)

private lemma actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (0 : ℂ), (-2 : ℂ), ?_⟩
  change completed 0 ≠ completed (-2)
  rw [completed_disk_cauchy.1.1 0 (by norm_num), completed_disk_cauchy.1.1 (-2) (by norm_num)]
  have hz : riemannZeta (-2) = 0 := by
    simpa using riemannZeta_neg_two_mul_nat_add_one 0
  intro he
  simp [transform, hz] at he
  have he' := congrArg Complex.re he
  norm_num [Complex.add_re, Complex.sub_re, Complex.div_re, Complex.normSq_apply] at he'
  linarith [Real.one_half_lt_eulerMascheroniConstant]

def evidence : Registration arena (type_of% @completed_disk_cauchy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨completed_disk_cauchy, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual shifted shifted_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@completed_disk_cauchy) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne.completed_disk_cauchy.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => completed) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne
