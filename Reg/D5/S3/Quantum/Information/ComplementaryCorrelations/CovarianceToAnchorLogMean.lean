import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchorLogMean

namespace Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchorLogMean

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Omega.CovarianceToAnchor
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ a b => logarithmicMean a b) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : ℝ}, 0 < a → 0 < b →
    R.readout () a b ≤ (a + b + 4 * Real.sqrt (a * b)) / 6

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (a := 1) (b := 1) zero_lt_one zero_lt_one
  change (2 : ℝ) ≤ (1 + 1 + 4 * Real.sqrt (1 * 1)) / 6 at hbad
  norm_num at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  change logarithmicMean 1 1 ≠ logarithmicMean 1 2
  have hlog : Real.log 2 < 1 := by
    simpa using Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≠ 1 by norm_num)
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [logarithmicMean, if_pos rfl, logarithmicMean, if_neg (by norm_num : (1 : ℝ) ≠ 2),
    Real.log_one, zero_sub]
  intro he
  have hc := (eq_div_iff (neg_ne_zero.mpr hp.ne')).mp he
  linarith

def family : Registration arena (type_of% @logarithmic_mean_le_simpson) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@logarithmic_mean_le_simpson, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@logarithmic_mean_le_simpson) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchorLogMean.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchorLogMean.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => logarithmicMean a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchorLogMean
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchorLogMean
