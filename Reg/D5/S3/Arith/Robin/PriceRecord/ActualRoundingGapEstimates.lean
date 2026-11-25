import D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates

open Real LeanInformationAudit
open _root_.D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Diagonal.MarginBound (bernoulliKL_pos)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p lam => integerGap p lam) (fun e => nomatch e)

private theorem chamber_low : (2 : ℝ) ^ (2 : ℕ) < cutoff (1 / 5) := by
  norm_num [cutoff]

private theorem chamber_high : cutoff (1 / 5) < (2 : ℝ) ^ (3 : ℕ) := by
  norm_num [cutoff]

private theorem chamber_gap_pos : 0 < integerGap 2 (1 / 5) := by
  have hc : cutoff (1 / 5) = 6 := by norm_num [cutoff]
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hlo : 2 * log 2 < log 6 := by
    have h := log_lt_log (by norm_num : (0 : ℝ) < 2 ^ (2 : ℕ))
      (by norm_num : (2 : ℝ) ^ (2 : ℕ) < 6)
    rw [log_pow] at h
    exact_mod_cast h
  have hhi : log 6 < 3 * log 2 := by
    have h := log_lt_log (by norm_num : (0 : ℝ) < 6)
      (by norm_num : (6 : ℝ) < 2 ^ (3 : ℕ))
    rw [log_pow] at h
    exact_mod_cast h
  have hcrit : 1 < critical 2 (1 / 5) ∧ critical 2 (1 / 5) < 2 := by
    rw [critical, hc]
    have hlow := (lt_div_iff₀ hlog).2 hlo
    have hhigh := (div_lt_iff₀ hlog).2 hhi
    exact ⟨by linarith, by linarith⟩
  have hf : ⌊critical 2 (1 / 5)⌋ = (1 : ℤ) :=
    Int.floor_eq_iff.mpr (by norm_num; exact ⟨hcrit.1.le, hcrit.2⟩)
  have he : ⌈critical 2 (1 / 5)⌉ = (2 : ℤ) :=
    Int.ceil_eq_iff.mpr (by norm_num; exact ⟨hcrit.1, hcrit.2.le⟩)
  have hprob1 : probability 2 1 = (4 : ℝ)⁻¹ := by norm_num [probability]
  have hprob2 : probability 2 2 = (8 : ℝ)⁻¹ := by norm_num [probability]
  rw [active_integer_gap (by norm_num) (by norm_num) chamber_low, hf, he, hc]
  norm_num only [Int.cast_ofNat, Int.cast_one]
  rw [hprob1, hprob2]
  exact lt_min
    (div_pos (bernoulliKL_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (by norm_num))
    (div_pos (bernoulliKL_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (by norm_num))

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 1 / 5, 1, ?_⟩
  change integerGap 2 (1 / 5) ≠ integerGap 2 1
  have hzero : integerGap 2 1 = 0 :=
    (inactive_loss (by norm_num) (by norm_num) (by norm_num [cutoff])
      (show (1 : ℝ) ≤ 1 from le_rfl)).2.1
  rw [hzero]
  exact chamber_gap_pos.ne'

namespace GlobalBounds

-- The nonnegativity claim is varied with the two actual upper bounds fixed.
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p lam : ℝ}, 1 < p → 0 < lam →
    0 ≤ R.readout () p lam ∧
      integerGap p lam ≤ lam * log p ∧
      integerGap p lam ≤ -log (1 - (p ^ (2 : ℕ))⁻¹)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hneg : (0 : ℝ) ≤ -1 := (h (p := 2) (lam := 1) (by norm_num) (by norm_num)).1
  norm_num at hneg

def family : Registration arena (type_of% (@integer_gap_global_bounds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integer_gap_global_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

end GlobalBounds

namespace ChamberIdentity

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p lam : ℝ}, 1 < p → 0 < lam →
    p ^ (2 : ℕ) < cutoff lam → cutoff lam < p ^ (3 : ℕ) →
    R.readout () p lam =
      min (-log (1 - (p ^ (2 : ℕ))⁻¹))
        (-log (1 - (p ^ (3 : ℕ))⁻¹) + lam * log p) -
      (-log (1 - (cutoff lam)⁻¹) + lam * log (cutoff lam / p ^ (2 : ℕ)))

def rejected : Realization signature :=
  realize signature (fun _ p lam => integerGap p lam + 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (p := 2) (lam := 1 / 5) (by norm_num) (by norm_num) chamber_low chamber_high
  change integerGap 2 (1 / 5) + 1 = _ at hbad
  have hok := integer_gap_chamber_identity (by norm_num) (by norm_num)
    chamber_low chamber_high
  linarith only [hbad, hok]

def family : Registration arena (type_of% (@integer_gap_chamber_identity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integer_gap_chamber_identity, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

end ChamberIdentity

namespace ChamberError

def errorBound (p lam : ℝ) : ℝ :=
  (cutoff lam)⁻¹ / (1 - (cutoff lam)⁻¹) +
    lam * log (cutoff lam / p ^ (2 : ℕ)) +
    ((p ^ (2 : ℕ))⁻¹) ^ 2 / (1 - (p ^ (2 : ℕ))⁻¹) +
    (p ^ (3 : ℕ))⁻¹ / (1 - (p ^ (3 : ℕ))⁻¹)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p lam : ℝ}, 1 < p → 0 < lam →
    p ^ (2 : ℕ) < cutoff lam → cutoff lam < p ^ (3 : ℕ) →
    |R.readout () p lam - min ((p ^ (2 : ℕ))⁻¹) (lam * log p)| ≤ errorBound p lam

def rejected : Realization signature := realize signature
  (fun _ p lam => min ((p ^ (2 : ℕ))⁻¹) (lam * log p) + errorBound p lam + 1)
  (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (p := 2) (lam := 1 / 5) (by norm_num) (by norm_num) chamber_low chamber_high
  let m := min (((2 : ℝ) ^ (2 : ℕ))⁻¹) (1 / 5 * log 2)
  change |m + errorBound 2 (1 / 5) + 1 - m| ≤ errorBound 2 (1 / 5) at hbad
  linarith only [(le_abs_self _).trans hbad]

def family : Registration arena (type_of% (@integer_gap_chamber_error)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integer_gap_chamber_error, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

end ChamberError

def globalBoundsAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integer_gap_global_bounds) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates.integer_gap_global_bounds.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates.GlobalBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨GlobalBounds.arena⟩
  objectArena := .source ⟨GlobalBounds.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source GlobalBounds.arena ⟨GlobalBounds.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p lam => integerGap p lam) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def chamberIdentityAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integer_gap_chamber_identity) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates.integer_gap_chamber_identity.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates.ChamberIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨ChamberIdentity.arena⟩
  objectArena := .source ⟨ChamberIdentity.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ChamberIdentity.arena ⟨ChamberIdentity.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p lam => integerGap p lam) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def chamberErrorAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integer_gap_chamber_error) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates.integer_gap_chamber_error.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates.ChamberError.family
  realizationSource := none
  generated := false
  arena := .source ⟨ChamberError.arena⟩
  objectArena := .source ⟨ChamberError.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ChamberError.arena ⟨ChamberError.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p lam => integerGap p lam) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates
