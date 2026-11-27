import D5.S3.Analytic.Resolvent.EntireLogDerivPowers
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
namespace Reg.D5.S3.Analytic.Resolvent.EntireLogDerivPowers
open _root_.D5.S3.Analytic.Resolvent.EntireLogDerivPowers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℂ)
    (fun _ => ℂ → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p F => ((-1 : ℂ) ^ p.1 / p.1.factorial) *
    iteratedDeriv p.1 (logDeriv F) p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℂ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {F : ℂ → ℂ} (_hF : Differentiable ℂ F) {α C : ℝ}
    (_hα : α < 2) (_hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α))
    (k : ℕ) (_hk : 1 ≤ k) {a : ℂ} (_ha : F a ≠ 0),
    HasSum (fun ρ : {z : ℂ // F z = 0} =>
      (analyticOrderNatAt F ρ.1 : ℂ) * (a - ρ.1)⁻¹ ^ (k + 1))
      (R.readout () ⟨k, a⟩ F)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (F := fun _ => 1) (by fun_prop) (α := 0) (C := 0)
    (by norm_num) (by intro z; norm_num) 1 (by norm_num) (a := 2) (by norm_num)
  have hn : IsEmpty {z : ℂ // (fun _ : ℂ => (1 : ℂ)) z = 0} :=
    ⟨fun z => one_ne_zero z.2⟩
  letI := hn
  have ht := hh.tsum_eq
  norm_num [rejected, realize] at ht

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 2⟩, (fun _ => 1), id, ?_⟩
  have hi : logDeriv (id : ℂ → ℂ) = fun z => z⁻¹ := by
    funext z
    simp [logDeriv_id]
  norm_num [actual, realize, iteratedDeriv_one, logDeriv_apply, hi, deriv_inv]

def family : Registration arena (type_of% @entire_logDeriv_power_hasSum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entire_logDeriv_power_hasSum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@entire_logDeriv_power_hasSum) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.Analytic.Resolvent.EntireLogDerivPowers.entire_logDeriv_power_hasSum
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Resolvent.EntireLogDerivPowers.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p F => ((-1 : ℂ) ^ p.1 / p.1.factorial) *
    iteratedDeriv p.1 (logDeriv F) p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Resolvent.EntireLogDerivPowers
    definition := none
    coordinates := #[6, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Resolvent.EntireLogDerivPowers
