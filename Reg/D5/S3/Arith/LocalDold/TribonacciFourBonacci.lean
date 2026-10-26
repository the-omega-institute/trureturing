import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.LocalDold.TribonacciFourBonacci
import Reg.Support.DependentFamily

/-! The actual prime-part observation in the complete paired source endpoint. -/

namespace Reg.D5.S3.Arith.LocalDold.TribonacciFourBonacci

open _root_.D5.S3.Arith.LocalDold.UnimodularObstruction
open _root_.D5.S3.Arith.LocalDold.TribonacciFourBonacci
open _root_.D5.S0.Tower.Tribonacci.Names
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ArithmeticFunction.Moebius

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : ℕ → ℕ), (a = tribonacci ∨ a = fourBonacci) →
    goodPrimes a = ∅ ∧
    ∀ p : ℕ, p.Prime → ∀ H : ℕ, ∃ q > H, q.Prime ∧
      0 < ∑ d ∈ q.divisors, (μ (q / d)) * (R.readout () p (a d) : ℤ) ∧
      (∑ d ∈ q.divisors, (μ (q / d)) * (R.readout () p (a d) : ℤ)) < q ∧
      ¬ (q : ℤ) ∣ ∑ d ∈ q.divisors, (μ (q / d)) * (R.readout () p (a d) : ℤ)

def actual : Realization signature :=
  realize signature (fun _ p n => pPart p n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq0, hq, hpos, hlt, hnd⟩ := (h tribonacci (Or.inl rfl)).2 2 Nat.prime_two 0
  change (0 : ℤ) < ∑ d ∈ q.divisors, (μ (q / d)) * (1 : ℤ) at hpos
  have hsum : (∑ d ∈ q.divisors, (μ (q / d)) * (1 : ℤ)) = 0 := by
    rw [show q = q ^ 1 by simp, Nat.divisors_prime_pow hq 1]
    norm_num [Finset.sum_range_succ]
    rw [ArithmeticFunction.moebius_apply_prime hq, Nat.div_self hq.pos]
    norm_num
  exact (by simpa only [hsum] using hpos : (0 : ℤ) < 0).false

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 1, 2, ?_⟩
  norm_num [actual, realize, pPart, padicValNat_self]

def registration : Registration arena
    (∀ (a : ℕ → ℕ), (a = tribonacci ∨ a = fourBonacci) →
    goodPrimes a = ∅ ∧
    ∀ p : ℕ, p.Prime → ∀ H : ℕ, ∃ q > H, q.Prime ∧
      0 < ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) ∧
      (∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ)) < q ∧
      ¬ (q : ℤ) ∣ ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ p n => pPart p n) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.LocalDold.TribonacciFourBonacci.result.audit
  realizationName := `Reg.D5.S3.Arith.LocalDold.TribonacciFourBonacci.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ p n => pPart p n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.LocalDold.TribonacciFourBonacci
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "body", "arg", "body",
        "arg", "arg", "fn", "arg", "arg", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.LocalDold.TribonacciFourBonacci
