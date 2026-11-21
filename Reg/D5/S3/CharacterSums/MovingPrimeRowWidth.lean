import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.MovingPrimeRowWidth
import Mathlib.Analysis.Complex.ExponentialBounds
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.CharacterSums.MovingPrimeRowWidth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.MovingPrimeRowWidth

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

/-- Squaring the window width is the change in (log x)² between its endpoints. -/
def squareWidth : Realization signature :=
  realize signature (fun _ _ b => b^2) (fun e => nomatch e)

def zeroWidth : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {q : ℕ}, q.Prime → q % 8 = 3 → 1 < Real.log q → ∀ {b : ℝ}, 1 < b →
    (HasPrimeRows q b ↔ V.readout () () b * (Real.log q)^(b-1) < 2)

private theorem zero_fails : ¬ arena.Law zeroWidth := by
  intro h
  have hL : 1 < Real.log (3 : ℝ) := (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hq : Nat.Prime 3 := by decide
  have hm : 3 % 8 = 3 := by decide
  have wrong := h (q := 3) hq hm hL (b := 2) (by norm_num)
  have rows : HasPrimeRows 3 2 := wrong.mpr (by change (0 : ℝ) * _ < 2; norm_num)
  have width := (prime_pair_power_window_iff hq hm hL (b := 2) (by norm_num)).mp rows
  norm_num at width
  linarith

def family : Registration arena (type_of% @prime_pair_power_window_iff) where
  actual := squareWidth
  bridge := Iff.rfl
  variation := ⟨@prime_pair_power_window_iff, zeroWidth, zero_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law squareWidth zeroWidth zero_fails
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    change (1 : ℝ)^2 ≠ 2^2
    norm_num

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_pair_power_window_iff) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.MovingPrimeRowWidth.prime_pair_power_window_iff "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.MovingPrimeRowWidth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => b^2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.MovingPrimeRowWidth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.CharacterSums.MovingPrimeRowWidth
