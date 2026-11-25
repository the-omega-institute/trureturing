import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.WeightedTail.SharpReserveLower
import Reg.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
import Reg.Support.SingleDependentReadout

/-! The strict lower reserve uses the same actual Robin log-margin realization
as the prime-band registration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Arith.Robin.WeightedTail.SharpReserveLower
  (sharp_lower_reserve_all_integers)
open _root_.D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)
open _root_.Reg.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (signature actual family)

namespace Reg.D5.S3.Arith.Robin.WeightedTail.SharpReserveLower

private def rejected : Realization signature :=
  realize signature (fun _ _ n => weightedTail psiErrorKernel (Real.log (n : ℝ)))
    (fun impossible => nomatch impossible)

def arena : Arena where
  signature := signature
  Law V := ∀ {ε : ℝ}, 0 < ε →
    ∃ Y : ℝ, 16 ≤ Y ∧ ∀ n : ℕ, Y ≤ Real.log (n : ℝ) →
      (2 * Real.sqrt 2 - 2 - ε) /
          (Real.sqrt (Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ))) <
        V.readout () () n - weightedTail psiErrorKernel (Real.log (n : ℝ))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Y, hY, hreserve⟩ := h (ε := 1 / 4) (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ := (hlog.eventually_ge_atTop Y).exists
  have hy := hY.trans hn
  have hsqrt : (5 : ℝ) / 4 ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hnum : 0 < 2 * Real.sqrt 2 - 2 - 1 / 4 := by linarith only [hsqrt]
  have hden : 0 < Real.sqrt (Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ)) :=
    mul_pos (Real.sqrt_pos.mpr (by linarith only [hy])) (Real.log_pos (by linarith only [hy]))
  have hbad := hreserve n hn
  change _ < weightedTail psiErrorKernel (Real.log (n : ℝ)) -
    weightedTail psiErrorKernel (Real.log (n : ℝ)) at hbad
  rw [sub_self] at hbad
  exact (not_lt_of_gt (div_pos hnum hden)) hbad

def evidence : Registration arena (type_of% @sharp_lower_reserve_all_integers) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sharp_lower_reserve_all_integers, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := family.dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sharp_lower_reserve_all_integers) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.WeightedTail.SharpReserveLower.sharp_lower_reserve_all_integers.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.WeightedTail.SharpReserveLower.evidence
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
    owner := `D5.S3.Arith.Robin.WeightedTail.SharpReserveLower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Arith.Robin.WeightedTail.SharpReserveLower
end
