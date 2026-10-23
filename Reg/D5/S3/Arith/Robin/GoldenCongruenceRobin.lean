import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.GoldenCongruenceRobin
import D5.S3.Arith.GoldenResource.GoldenCell5040Congruence
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.GoldenCongruenceRobin

open _root_.D5.S3.Arith.Robin.GoldenCongruenceRobin
open _root_.D5.S3.Arith.GoldenResource.GoldenCell5040Congruence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 5040 < n → 5040 ∣ n → Nat.ModEq n (3 ^ n) 2241 →
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * R.readout () () (Real.log (n : ℝ))

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hmod := goldenCell5040_modEq_2241 10080 (by decide)
  have hbad := h (n := 10080) (by norm_num) (by decide) hmod
  change (ArithmeticFunction.sigma 1 10080 : ℝ) / (10080 : ℕ) <
    Real.exp Real.eulerMascheroniConstant * 0 at hbad
  rw [mul_zero] at hbad
  exact absurd hbad (not_lt.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num)).ne

def registration : Registration arena (type_of% (@robin_of_modEq_2241)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨robin_of_modEq_2241, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@robin_of_modEq_2241)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.GoldenCongruenceRobin.robin_of_modEq_2241.audit
  realizationName := `Reg.D5.S3.Arith.Robin.GoldenCongruenceRobin.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GoldenCongruenceRobin
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end

end Reg.D5.S3.Arith.Robin.GoldenCongruenceRobin
