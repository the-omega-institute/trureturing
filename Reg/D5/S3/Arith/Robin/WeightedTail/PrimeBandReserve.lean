import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.WeightedTail.PrimeBandReserve
import Reg.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
import Reg.Support.SingleDependentReadout

/-! The prime-band reserve observes the integer's actual Robin log margin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Arith.Robin.WeightedTail.PrimeBandReserve
  (primeBand primeBand_reserve_le_robinLogSlack)
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)
open _root_.D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open _root_.Reg.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (signature actual family)

namespace Reg.D5.S3.Arith.Robin.WeightedTail.PrimeBandReserve

private def rejected : Realization signature :=
  realize signature (fun _ _ n => weightedTail psiErrorKernel (Real.log (n : ℝ)))
    (fun impossible => nomatch impossible)

def arena : Arena where
  signature := signature
  Law V := ∀ {n : ℕ}, 16 ≤ Real.log (n : ℝ) →
    ((primeBand (Real.log (n : ℝ))).card : ℝ) / (16 * Real.log (n : ℝ)) ≤
      V.readout () () n - weightedTail psiErrorKernel (Real.log (n : ℝ))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  let n : ℕ := 2 ^ 24
  let y : ℝ := Real.log (n : ℝ)
  have hy_log : y = 24 * Real.log 2 := by
    change Real.log (↑((2 : ℕ) ^ 24) : ℝ) = _
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hlog_lower : (2 : ℝ) / 3 < Real.log 2 := by
    simpa only [mul_one, show (1 : ℝ) + 2 = 3 by norm_num,
      show (1 : ℝ) + 1 = 2 by norm_num] using
      (Real.lt_log_one_add_of_pos (x := 1) zero_lt_one)
  have hlog_upper : Real.log (2 : ℝ) < 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      (Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num))
  have hy : 16 ≤ y := by linarith only [hy_log, hlog_lower]
  have hy_lt : y < 24 := by linarith only [hy_log, hlog_upper]
  have hlower : Real.sqrt (2 * y) < (7 : ℝ) :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num <;> linarith only [hy_lt])
  have hsqrt : (4 : ℝ) ≤ Real.sqrt y :=
    Real.le_sqrt_of_sq_le (by norm_num <;> exact hy)
  have hupper : (7 : ℝ) ≤ 2 * Real.sqrt y := by linarith only [hsqrt]
  have hlower_floor : ⌊Real.sqrt (2 * y)⌋₊ < 7 :=
    (Nat.floor_lt (Real.sqrt_nonneg _)).mpr (by simpa only [Nat.cast_ofNat] using hlower)
  have hupper_floor : 7 ≤ ⌊2 * Real.sqrt y⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_ofNat] using hupper)
  have hseven : 7 ∈ primeBand y := by
    have hprime : Nat.Prime 7 := by norm_num
    unfold primeBand
    refine Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hupper_floor, hprime⟩, ?_⟩
    intro hmem
    exact (not_le_of_gt hlower_floor) (Nat.mem_primesLE.mp hmem).1
  have hcard : (0 : ℝ) < ((primeBand y).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨7, hseven⟩)
  have hy_pos : 0 < y := by linarith only [hy]
  have hreserve : 0 < ((primeBand y).card : ℝ) / (16 * y) :=
    div_pos hcard (mul_pos (by norm_num) hy_pos)
  have hbad := h (n := n) hy
  change ((primeBand y).card : ℝ) / (16 * y) ≤
    weightedTail psiErrorKernel y - weightedTail psiErrorKernel y at hbad
  exact (not_le_of_gt hreserve) (by simpa only [sub_self] using hbad)

def evidence : Registration arena (type_of% @primeBand_reserve_le_robinLogSlack) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨primeBand_reserve_le_robinLogSlack, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := family.dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@primeBand_reserve_le_robinLogSlack) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.WeightedTail.PrimeBandReserve.primeBand_reserve_le_robinLogSlack.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.WeightedTail.PrimeBandReserve.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout :=
    some (realize signature (fun _ _ n => robinLogMargin n) (fun impossible => nomatch impossible))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.WeightedTail.PrimeBandReserve
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Arith.Robin.WeightedTail.PrimeBandReserve
end
