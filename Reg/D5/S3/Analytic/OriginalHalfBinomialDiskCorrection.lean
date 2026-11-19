import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
import Reg.Support.SingleDependentReadout

/-! Typed observation families for the complete native continuation statements. -/

noncomputable section
open scoped Classical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open scoped Topology

namespace Reg.D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod (period)
open _root_.D5.S3.Analytic.OriginalHalfBinomialWronskian (tau)
open _root_.D5.S3.Analytic.OriginalHalfBinomialDiskCorrection

namespace Correction
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Unit) (fun _ => ℂ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ z => decide (z = 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law M :=
    M.readout () () (period 0) = true ∧ deriv period 0 = 1 / 4 ∧
    R 0 = 1 ∧ deriv R 0 = 1 / 2 ∧
    DifferentiableOn ℂ R disk ∧ DifferentiableOn ℂ G disk ∧ G 0 = 1 / 2 ∧
    (∀ r : ℂ, r * G r = R r - 1) ∧
    H 0 = 0 ∧ (∀ r ∈ disk, HasDerivAt H (-Complex.I / (Real.pi : ℂ) * G r) r) ∧
    deriv H 0 = -Complex.I / (2 * (Real.pi : ℂ)) ∧
    (∀ h : ℂ → ℂ, h 0 = 0 →
      (∀ r ∈ disk, HasDerivAt h (-Complex.I / (Real.pi : ℂ) * G r) r) → EqOn h H disk)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simpa [rejected, realize] using h.1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @disk_correction) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @disk_correction,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@disk_correction) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialDiskCorrection.Correction.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialDiskCorrection.Correction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => decide (z = 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Correction

end Reg.D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
