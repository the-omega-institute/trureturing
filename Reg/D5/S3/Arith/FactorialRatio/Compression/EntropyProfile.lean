import D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyProfile

open Finset Real Set
open scoped Topology
open LeanInformationAudit
open _root_.D5.S3.Arith.FactorialRatio.CompactFactorialGcd
open _root_.D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Profile

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => entropyIntegral t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -Real.eulerMascheroniConstant - 1) (fun e => nomatch e)

/-- Only the value in the strict gamma gap is varied; all other clauses are retained. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    Continuous entropyIntegral ∧ entropyIntegral 0 = 0 ∧ entropyIntegral 1 = -1 / 2 ∧
      (∀ t : ℝ, 0 < t → t ≤ 1 → entropyIntegral t =
        t / 2 * log t - (1 - t) ^ 2 / (2 * t) * log (1 - t) - 1 / 2) ∧
      (∃! t : ℝ, t ∈ Set.Icc 0 1 ∧ ∀ v ∈ Set.Icc 0 1, entropyIntegral t ≤ entropyIntegral v) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, -(log 2 - 1 / 8) ≤ entropyIntegral t ∧
        0 < Real.eulerMascheroniConstant + R.readout () () t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h.2.2.2.2.2 0 (by simp)).2
  change 0 < Real.eulerMascheroniConstant + (-Real.eulerMascheroniConstant - 1) at hh
  linarith

def family : Registration arena (type_of% @entropy_profile) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨entropy_profile, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change entropyIntegral 0 ≠ entropyIntegral 1
    rw [entropy_profile.2.1, entropy_profile.2.2.1]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@entropy_profile) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.EntropyProfile.entropy_profile.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyProfile.Profile.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => entropyIntegral t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "arg", "body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Profile

namespace FiniteTerm

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ)
    (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p b => selbergFactorial p.1 p.2 b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r s b : ℕ), r * b ≤ s →
    (r : ℝ) * s * (log s - 1 - 41 / 72) -
        2 * (r : ℝ) * (log ((s : ℝ) + 1) + 1) ≤ log (R.readout () ⟨r, s⟩ b : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 16 0 (by decide)
  simp only [rejected, realize, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hh
  change (1 : ℝ) * 16 * (log 16 - 1 - 41 / 72) -
    2 * 1 * (log (16 + 1) + 1) ≤ log 0 at hh
  have hl16 : log (16 : ℝ) = 4 * log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  have hl17 : log (17 : ℝ) ≤ 5 * log 2 := by
    have hh' := Real.log_le_log (by norm_num : (0 : ℝ) < 17)
      (by norm_num : (17 : ℝ) ≤ 2 ^ 5)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh'
  norm_num only [one_mul, zero_add, Real.log_zero] at hh
  rw [hl16] at hh
  linarith [Real.log_two_gt_d9]

def family : Registration arena (type_of% @compact_single_term_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨compact_single_term_lower_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨⟨2, 3⟩, 0, 1, ?_⟩
    change selbergFactorial 2 3 0 ≠ selbergFactorial 2 3 1
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@compact_single_term_lower_bound) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.EntropyProfile.compact_single_term_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyProfile.FiniteTerm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p b => selbergFactorial p.1 p.2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteTerm

namespace Window

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ M b => selbergFactorial (M + 1) (M * (M - 1)) b)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M b : ℕ), 2 ≤ M → (M + 1) * b ≤ M * (M - 1) →
    0 < Real.eulerMascheroniConstant - 41 / 72 ∧
      (Real.eulerMascheroniConstant - 41 / 72) * (M : ℝ) ^ 2 -
          8 * (M : ℝ) * (log ((M : ℝ) + 1) + 1) ≤
        log (R.readout () M b : ℝ) / M -
          ((M : ℝ) ^ 2 * log ((M : ℝ) ^ 2) -
            (1 + Real.eulerMascheroniConstant) * (M : ℝ) ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 16 0 (by decide) (by decide)).2
  simp only [rejected, realize, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hh
  change (Real.eulerMascheroniConstant - 41 / 72) * (16 : ℝ) ^ 2 -
      8 * 16 * (log ((16 : ℝ) + 1) + 1) ≤
    log 0 / 16 - ((16 : ℝ) ^ 2 * log ((16 : ℝ) ^ 2) -
      (1 + Real.eulerMascheroniConstant) * (16 : ℝ) ^ 2) at hh
  have hl256 : log ((16 : ℝ) ^ 2) = 8 * log 2 := by
    convert Real.log_pow (2 : ℝ) 8 using 1 <;> norm_num
  have hl17 : log (17 : ℝ) ≤ 5 * log 2 := by
    have hh' := Real.log_le_log (by norm_num : (0 : ℝ) < 17)
      (by norm_num : (17 : ℝ) ≤ 2 ^ 5)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh'
  rw [hl256] at hh
  norm_num only [Real.log_zero, zero_div] at hh
  linarith [Real.log_two_gt_d9]

def family : Registration arena (type_of% @quadratic_window_obstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨quadratic_window_obstruction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨3, 0, 1, ?_⟩
    change selbergFactorial 4 6 0 ≠ selbergFactorial 4 6 1
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quadratic_window_obstruction) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.EntropyProfile.quadratic_window_obstruction.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyProfile.Window.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ M b => selbergFactorial (M + 1) (M * (M - 1)) b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Window
namespace StrictConvexity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => entropyIntegral t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := StrictConvexOn ℝ (Set.Icc 0 1) (fun t => R.readout () () t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp) (by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  change (0 : ℝ) < (1 / 2) • 0 + (1 / 2) • 0 at hh
  norm_num at hh

def family : Registration arena (type_of% @profile_strictConvex) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨profile_strictConvex, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change entropyIntegral 0 ≠ entropyIntegral 1
    rw [entropy_profile.2.1, entropy_profile.2.2.1]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@profile_strictConvex) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.EntropyProfile.profile_strictConvex.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyProfile.StrictConvexity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => entropyIntegral t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end StrictConvexity

end Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
