import D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- The compact-margin audit preserves the complete source telescope and changes
only its actual raw-margin readout. The other two source-bound audits still require
whole-family variation, sensitivity, observational dependence and producer bindings. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual

open Real
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit


namespace compact_second_raw_margin

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ X t => secondRawMargin X t) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X K s : ℝ} (hX : 1 < X) (hK : 0 ≤ K)
    (hs : |s| ≤ K) (hlarge : 2 * K ≤ sqrt 2 * log X)
    (ht : 1 < secondTubePoint X s),
    |X * log X * V.readout () X (secondTubePoint X s) +
      s / sqrt 2 + log (sqrt 2)| ≤ secondExpansionError X K

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.compact_second_raw_margin

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.compact_second_raw_margin)) ↔ arena.Law actual := Iff.rfl

private def rejected : Realization signature :=
  realize signature (fun _ X _ =>
    (secondExpansionError X 0 + |log (sqrt 2)| + 1) / (X * log X))
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have ha2 : sqrt (2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have ha1 : 1 < sqrt (2 : ℝ) := by nlinarith
  have hL : 0 < log (4 : ℝ) := log_pos (by norm_num)
  have ht : 1 < secondTubePoint 4 0 := by
    norm_num [secondTubePoint]
    nlinarith
  have hb := h (X := 4) (K := 0) (s := 0) (by norm_num) le_rfl
    (by simp) (by simpa only [mul_zero] using mul_nonneg ha.le hL.le) ht
  change |4 * log 4 * ((secondExpansionError 4 0 + |log (sqrt 2)| + 1) /
    (4 * log 4)) + 0 / sqrt 2 + log (sqrt 2)| ≤ secondExpansionError 4 0 at hb
  rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hL.ne')] at hb
  have hl : 0 < log (sqrt (2 : ℝ)) := log_pos ha1
  have hlo := (le_abs_self (secondExpansionError 4 0 + |log (sqrt 2)| + 1 +
    0 / sqrt 2 + log (sqrt 2))).trans hb
  simp only [zero_div, add_zero, abs_of_pos hl] at hlo
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 2, 3, ?_⟩
  change secondRawMargin 1 2 ≠ secondRawMargin 1 3
  norm_num [secondRawMargin]
  exact ne_of_gt (log_lt_log (by norm_num) (by norm_num))

def family : Registration arena
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.compact_second_raw_margin)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.compact_second_raw_margin)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.compact_second_raw_margin.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.compact_second_raw_margin.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ X t => secondRawMargin X t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end compact_second_raw_margin


end Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
