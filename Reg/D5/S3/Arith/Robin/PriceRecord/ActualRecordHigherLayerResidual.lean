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


open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)

namespace actual_record_critical_residual

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ X m => actualDefect X m - completeFirstLayerLoss X m)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ ε : ℝ, 0 < ε → ∃ X0 : ℝ, 1 < X0 ∧
    ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
    (∀ k : ℕ, 0 < k → k < m →
      goldenResourceObjective mu k < goldenResourceObjective mu m) →
    X0 ≤ log (m : ℝ) →
    let X := log (m : ℝ)
    0 ≤ sqrt X * log X ^ 3 * V.readout () X m ∧
    sqrt X * log X ^ 3 * V.readout () X m < ε

private theorem actual_law : arena.Law actual :=
  _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.actual_record_critical_residual

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.actual_record_critical_residual)) ↔
      arena.Law actual := Iff.rfl

/-- Concrete whole-family intervention; it fails at arbitrarily large literal
records. No artificial finite sample or selected price is used. -/
private def negative : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem negative_not_law : ¬ arena.Law negative := by
  intro h
  obtain ⟨X0, hX01, hX0⟩ := h 1 (by norm_num)
  obtain ⟨n, mu, hn, hmu, hrecord, hP⟩ :=
    _root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.arbitrarily_large_price_records
      (exp (max X0 2))
  have hPn : largestPrime n ≤ n := by
    change n.primeFactors.sup id ≤ n
    exact sup_le (fun p hp => Nat.le_of_dvd (by omega : 0 < n)
      (Nat.dvd_of_mem_primeFactors hp))
  have hPnR : (largestPrime n : ℝ) ≤ n := by exact_mod_cast hPn
  have hX : max X0 2 < log (n : ℝ) := by
    have hh := log_lt_log (exp_pos (max X0 2)) (hP.trans_le hPnR)
    simpa only [log_exp] using hh
  have hx1 : 1 < log (n : ℝ) := by linarith [le_max_right X0 (2 : ℝ)]
  have hscale : 0 < sqrt (log (n : ℝ)) * log (log (n : ℝ)) ^ 3 :=
    mul_pos (sqrt_pos.mpr (by linarith)) (pow_pos (log_pos hx1) 3)
  have hh := hX0 n hn mu hmu hrecord ((le_max_left X0 2).trans hX.le)
  change 0 ≤ sqrt (log (n : ℝ)) * log (log (n : ℝ)) ^ 3 * (-1) ∧ _ at hh
  nlinarith [hh.1]

private theorem variation_candidate : Variation arena actual :=
  ⟨actual_law, negative, negative_not_law⟩

private theorem sensitivity_candidate : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨negative, ?_, rfl, negative_not_law⟩
    intro j hji
    exact False.elim (hji (Subsingleton.elim j i))
  · intro e
    exact nomatch e

/- Remaining exact audit gap: ObservationalDependence signature actual on a
lawful scoped reconstruction, exact sourceSelection, and producer binding.
The two evidence candidates above are source terms, not validated registration.
No Contract.Registration or declared_validated claim is supplied. -/

end actual_record_critical_residual

#check @_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.actual_record_critical_residual
#print axioms _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.actual_record_critical_residual
#print axioms actual_record_critical_residual.actual_law
#print axioms actual_record_critical_residual.source_bridge
#print axioms actual_record_critical_residual.variation_candidate
#print axioms actual_record_critical_residual.sensitivity_candidate

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
