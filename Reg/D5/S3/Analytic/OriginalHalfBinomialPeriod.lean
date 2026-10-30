import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.OriginalHalfBinomialPeriod
import Reg.Support.SingleDependentReadout

/-! A source-bound period-value intervention for the full analytic equation. -/

noncomputable section
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.OriginalHalfBinomialPeriod

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => period z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Vary the final period-value occurrence, retaining the complete original law. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {z : ℂ}, ‖z‖ < 1 →
    DifferentiableAt ℂ period z ∧ DifferentiableAt ℂ (deriv period) z ∧
      z * (1 - z) * deriv (deriv period) z +
        (1 - 2 * z) * deriv period z - (1 / 4 : ℂ) * R.readout () () z = 0

private theorem period_zero : period 0 = 1 := by
  calc
    period 0 = (halfBinomial 0) ^ 2 * (0 : ℂ) ^ 0 :=
      tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])
    _ = 1 := by simp [halfBinomial]

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have ha := (picard_fuchs (z := 0) (by norm_num)).2.2
  have hb := (h (z := 0) (by norm_num)).2.2
  norm_num [period_zero] at ha
  norm_num [rejected, realize] at hb
  rw [hb] at ha
  norm_num at ha

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  by_contra h
  push_neg at h
  have he : period = fun _ : ℂ => (1 : ℂ) := by
    funext z
    exact (h () z 0).trans period_zero
  have ha := (picard_fuchs (z := 0) (by norm_num)).2.2
  norm_num [he] at ha

def evidence : Registration arena (type_of% @picard_fuchs) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@picard_fuchs, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@picard_fuchs) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialPeriod.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialPeriod.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => period z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialPeriod
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.OriginalHalfBinomialPeriod
