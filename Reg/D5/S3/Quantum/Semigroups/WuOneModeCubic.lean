import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuOneModeCubic
import Batteries.Tactic.OpenPrivate

/-! Source-bound readout of the temperature argument of the one-mode premise. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuOneModeCubic
open _root_.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private gamma h c e bias gibbsLow gibbsHigh cutA cutB entropyPair from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

namespace Reg.D5.S3.Quantum.Semigroups.WuOneModeCubic

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ r => r) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ r => -(3 / 2) * r) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 1 ≤ r → OneModeBound (W.readout () () r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  have hone : OneModeBound (-(3 / 2 : ℝ)) := by
    simpa only [rejected, realize, mul_one] using hlaw (r := 1) le_rfl
  have halpha : 0 ≤ alpha (-(3 / 2 : ℝ)) := by
    have hlog : 0 < Real.log (-(3 / 2 : ℝ)) := Real.log_pos_of_lt_neg_one (by norm_num)
    rw [alpha, if_neg (by norm_num : -(3 / 2 : ℝ) ≠ 1)]
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) hlog.le)
  have hlogs : Real.log (-(864 / 361 : ℝ)) +
      (Real.log (1 / 2 : ℝ) + Real.log (1 / 2 : ℝ)) ≤ 0 := by
    have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
    rw [← Real.log_mul hhalf hhalf,
      ← Real.log_mul (by norm_num : -(864 / 361 : ℝ) ≠ 0) (mul_ne_zero hhalf hhalf)]
    exact (Real.log_neg_of_lt_zero (by norm_num) (by norm_num)).le
  have hformula : oneModeDeficit (-(3 / 2 : ℝ)) 0 1 (-1) =
      -(153 / 1064) + alpha (-(3 / 2 : ℝ)) / 2 *
        (Real.log (-(864 / 361 : ℝ)) + (Real.log (1 / 2 : ℝ) + Real.log (1 / 2 : ℝ))) := by
    norm_num [oneModeDeficit, entropyPair, h, gamma, gibbsLow, gibbsHigh, cutA, cutB, c, e, bias] <;>
      ring
  have hneg : oneModeDeficit (-(3 / 2 : ℝ)) 0 1 (-1) < 0 := by
    rw [hformula]
    exact add_neg_of_neg_of_nonpos (by norm_num)
      (mul_nonpos_of_nonneg_of_nonpos (div_nonneg halpha (by norm_num)) hlogs)
  exact hneg.not_ge (hone 0 1 (-1) le_rfl zero_le_one le_rfl (by norm_num))

def family : Registration arena (type_of% @one_mode_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@one_mode_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@one_mode_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuOneModeCubic.one_mode_bound.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuOneModeCubic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuOneModeCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Semigroups.WuOneModeCubic
