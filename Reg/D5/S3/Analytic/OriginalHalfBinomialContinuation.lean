import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.OriginalHalfBinomialContinuation
import Reg.Support.SingleDependentReadout

/-! Typed observation families for the complete native continuation statements. -/

noncomputable section
open scoped Classical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open scoped Topology

namespace Reg.D5.S3.Analytic.OriginalHalfBinomialContinuation
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod (period)
open _root_.D5.S3.Analytic.OriginalHalfBinomialWronskian (tau)
open _root_.D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
open _root_.D5.S3.Analytic.OriginalHalfBinomialContinuation

namespace Continuation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ) (fun _ => ℂ → ℂ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ r f => decide (HasDerivAt f (-Complex.I / ((Real.pi : ℂ) * r * (1 - r) * period r ^ 2)) r)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law M :=
    (∀ r ∈ slitDisk, M.readout () r t0 = true) ∧
    EqOn t0 tau lens

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.1 (1 / 2) (by norm_num [slitDisk, disk, Complex.mem_slitPlane_iff])
  simpa [rejected, realize] using hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ : ℂ => (0 : ℂ)), (fun z : ℂ => z), ?_⟩
  have hn : ¬ HasDerivAt (fun z : ℂ => z) (0 : ℂ) 0 := by
    intro h
    have he := h.unique (hasDerivAt_id (0 : ℂ))
    norm_num at he
  simp [actual, realize, hn, hasDerivAt_const]

def family : Registration arena (type_of% @actual_continuation) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @actual_continuation,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_continuation) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialContinuation.Continuation.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialContinuation.Continuation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r f => decide (HasDerivAt f (-Complex.I / ((Real.pi : ℂ) * r * (1 - r) * period r ^ 2)) r)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialContinuation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Continuation

namespace Numerator
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ) (fun _ => ℂ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ r z => decide (z = Complex.I * period (1 - r))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law M :=
    DifferentiableOn ℂ n0 slitDisk ∧
    (∀ r ∈ lens, M.readout () r (n0 r) = true) ∧
    (∀ r ∈ slitDisk, DifferentiableAt ℂ (deriv n0) r ∧
      r * (1 - r) * deriv (deriv n0) r +
        (1 - 2 * r) * deriv n0 r - (1 / 4 : ℂ) * n0 r = 0 ∧
      deriv n0 r * period r - n0 r * deriv period r =
        -Complex.I / ((Real.pi : ℂ) * r * (1 - r)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.2.1 (1 / 2) (by norm_num [lens, Metric.mem_ball, dist_eq_norm])
  simpa [rejected, realize] using hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, Complex.I, ?_⟩
  simp [actual, realize, disk_correction.1, Ne.symm Complex.I_ne_zero]

def family : Registration arena (type_of% @continued_numerator) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @continued_numerator,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continued_numerator) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialContinuation.Numerator.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialContinuation.Numerator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r z => decide (z = Complex.I * period (1 - r))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialContinuation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Numerator

end Reg.D5.S3.Analytic.OriginalHalfBinomialContinuation
