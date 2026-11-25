import D5.S3.Arith.FactorialRatio.RankOneLCMGcd
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The tail and prefix products retain their dependence on the window endpoint. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.RankOneLCMGcd

open _root_.D5.S3.Arith.FactorialRatio.RankOneLCMGcd
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset
open scoped Nat

abbrev signature := Reg.Support.SingleDependentReadout.signature ℕ
  (fun _ => ℕ) (fun _ => ℕ)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

namespace Tail

def actual : Realization signature :=
  realize signature (fun _ H M => tailLCM H M) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H M : ℕ), M ≤ H →
    R.readout () H M =
      (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).gcd factorialProduct

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 0 (by decide)
  have hgood := tailLCM_eq_gcd 0 0 (by decide)
  have ht : tailLCM 0 0 = 1 := by simp [tailLCM]
  change 0 = _ at hbad
  rw [ht] at hgood
  exact Nat.zero_ne_one (hbad.trans hgood.symm)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 0, 1, ?_⟩
  change tailLCM 2 0 ≠ tailLCM 2 1
  decide

def family : Registration arena (type_of% @tailLCM_eq_gcd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tailLCM_eq_gcd, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@tailLCM_eq_gcd) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.RankOneLCMGcd.tailLCM_eq_gcd.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.RankOneLCMGcd.Tail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ H M => tailLCM H M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.RankOneLCMGcd
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Tail

namespace Prefix

def actual : Realization signature :=
  realize signature (fun _ H M => prefixLCM H M) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H M : ℕ), M ≤ H →
    R.readout () H M = H ! / (H - M)! *
      (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).lcm
        (Nat.multinomial Finset.univ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 0 (by decide)
  have hgood := prefixLCM_eq_factorial_ratio_mul_multinomial_lcm 0 0 (by decide)
  have ht : prefixLCM 0 0 = 1 := by simp [prefixLCM]
  change 0 = _ at hbad
  rw [ht] at hgood
  exact Nat.zero_ne_one (hbad.trans hgood.symm)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 0, 1, ?_⟩
  change prefixLCM 2 0 ≠ prefixLCM 2 1
  decide

def family : Registration arena (type_of% @prefixLCM_eq_factorial_ratio_mul_multinomial_lcm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prefixLCM_eq_factorial_ratio_mul_multinomial_lcm, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prefixLCM_eq_factorial_ratio_mul_multinomial_lcm) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.RankOneLCMGcd.prefixLCM_eq_factorial_ratio_mul_multinomial_lcm.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.RankOneLCMGcd.Prefix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ H M => prefixLCM H M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.RankOneLCMGcd
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Prefix
end Reg.D5.S3.Arith.FactorialRatio.RankOneLCMGcd
