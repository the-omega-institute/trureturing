import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.OriginalHalfBinomialProjective
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open scoped Topology

namespace Reg.D5.S3.Analytic.OriginalHalfBinomialProjective
open _root_.D5.S3.Analytic.OriginalHalfBinomialProjective
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod (period)
open _root_.D5.S3.Analytic.OriginalHalfBinomialWronskian (tau)
open _root_.D5.S3.Analytic.AbelRatioSchwarzian (preSchwarzian schwarzian)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ z => decide (z ≠ 0)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ z => false) (fun e => nomatch e)

/-- The complete original telescope and all conclusions; only the selected
native observation is varied. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℂ) (hr : ‖r‖ < 1) (hc : ‖1 - r‖ < 1) ,
    R.readout () () (deriv tau r) = true ∧
      HasDerivAt (deriv tau)
        ((-(1 - 2 * r) / (r * (1 - r)) - 2 * (deriv period r / period r)) *
          deriv tau r) r ∧
      DifferentiableAt ℂ (deriv (deriv tau)) r ∧
      preSchwarzian tau r =
        -(1 - 2 * r) / (r * (1 - r)) - 2 * (deriv period r / period r) ∧
      schwarzian tau r = (1 - r + r ^ 2) / (2 * r ^ 2 * (1 - r) ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (1 / 2) (by norm_num) (by norm_num)
  simpa [rejected, realize] using hh.1


private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @original_tau_projective) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro r hr hc
    simpa only [actual, realize, decide_eq_true_eq] using original_tau_projective hr hc,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_tau_projective) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialProjective.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialProjective.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => decide (z ≠ 0)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialProjective
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.OriginalHalfBinomialProjective
