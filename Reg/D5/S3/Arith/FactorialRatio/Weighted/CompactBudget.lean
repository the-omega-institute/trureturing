import D5.S3.Arith.FactorialRatio.Weighted.CompactBudget
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FactorialRatio.Weighted.CompactBudget

open _root_.D5.S3.Arith.FactorialRatio.Weighted.CompactBudget
open _root_.D5.S3.Arith.FactorialRatio.Compression.SharpLoss
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Weights := ℕ → ℕ → ℕ

private theorem zero_excess : compactWeightedExcess 3 8 (fun _ _ => 0) = 1 := by
  rw [compactWeightedExcess_eq_weightedExcess (by decide)]
  decide

private theorem unit_excess : compactWeightedExcess 3 8 (fun _ _ => 1) = 2 := by
  rw [compactWeightedExcess_eq_weightedExcess (by decide)]
  decide

private theorem excess_separation :
    compactWeightedExcess 3 8 (fun _ _ => 0) ≠ compactWeightedExcess 3 8 (fun _ _ => 1) := by
  rw [zero_excess, unit_excess]
  decide

namespace Exponent
abbrev signature : Signature where
  Params := ℕ × ℕ × ℕ
  State _ := Weights
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z c => (compactWeightedExcess z.1 z.2.1 c).factorization z.2.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r s p : ℕ}, 2 ≤ r → ∀ (c : Weights), p ∈ Nat.primesLE (compactHeight r s) →
    R.readout () (r, s, p) c =
      _root_.D5.S3.Arith.FactorialRatio.Compression.SharpLoss.weightedPrimeLoss
        r s p (Nat.log p s + 1) (c p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 2) (s := 1) (p := 2) (by decide) (fun _ _ => 0) (by decide)
  change 1 = _root_.D5.S3.Arith.FactorialRatio.Compression.SharpLoss.weightedPrimeLoss
    2 1 2 (Nat.log 2 1 + 1) (fun _ => 0) at hh
  exact (by decide : ¬ 1 =
    _root_.D5.S3.Arith.FactorialRatio.Compression.SharpLoss.weightedPrimeLoss
      2 1 2 (Nat.log 2 1 + 1) (fun _ => 0)) hh

def family : Registration arena (type_of% @compactWeightedExcess_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@compactWeightedExcess_factorization, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨(3, 8, 2), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
    change (compactWeightedExcess 3 8 (fun _ _ => 0)).factorization 2 ≠
      (compactWeightedExcess 3 8 (fun _ _ => 1)).factorization 2
    rw [zero_excess, unit_excess, Nat.factorization_one,
      Finsupp.zero_apply, Nat.prime_two.factorization_self]
    decide
end Exponent

def exponentAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@compactWeightedExcess_factorization) (Realization Exponent.signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.Weighted.CompactBudget.compactWeightedExcess_factorization.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompactBudget.Exponent.family
  realizationSource := none
  generated := false
  arena := .source ⟨Exponent.arena⟩
  objectArena := .source ⟨Exponent.arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source Exponent.arena ⟨Exponent.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Exponent.signature
    (fun _ z c => (compactWeightedExcess z.1 z.2.1 c).factorization z.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Weighted.CompactBudget
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Identity
abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := Weights
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z c => compactWeightedExcess z.1 z.2 c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r s : ℕ}, 2 ≤ r → ∀ (c : Weights), R.readout () (r, s) c =
    _root_.D5.S3.Arith.FactorialRatio.Compression.SharpLoss.weightedExcess
      r s (Nat.primesLE (compactHeight r s)) c

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 2) (s := 0) (by decide) (fun _ _ => 0)
  change 0 = _root_.D5.S3.Arith.FactorialRatio.Compression.SharpLoss.weightedExcess
    2 0 (Nat.primesLE (compactHeight 2 0)) (fun _ _ => 0) at hh
  exact (by decide : ¬ 0 =
    _root_.D5.S3.Arith.FactorialRatio.Compression.SharpLoss.weightedExcess
      2 0 (Nat.primesLE (compactHeight 2 0)) (fun _ _ => 0)) hh

def family : Registration arena (type_of% @compactWeightedExcess_eq_weightedExcess) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@compactWeightedExcess_eq_weightedExcess, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨(3, 8), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
    simpa only [actual, realize] using excess_separation
end Identity

def identityAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@compactWeightedExcess_eq_weightedExcess) (Realization Identity.signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.Weighted.CompactBudget.compactWeightedExcess_eq_weightedExcess.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompactBudget.Identity.family
  realizationSource := none
  generated := false
  arena := .source ⟨Identity.arena⟩
  objectArena := .source ⟨Identity.arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source Identity.arena ⟨Identity.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Identity.signature
    (fun _ z c => compactWeightedExcess z.1 z.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Weighted.CompactBudget
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Shared
abbrev signature : Signature where
  Params := ℕ × ℕ × ℕ
  State _ := Weights × Weights
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role z w => compactWeightedExcess z.1 z.2.1
    (if role then w.2 else w.1)) (fun e => nomatch e)

def rejected (role : Bool) : Realization signature :=
  realize signature (fun i z w => if i = role then 0 else
    compactWeightedExcess z.1 z.2.1 (if i then w.2 else w.1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r s C : ℕ}, 2 ≤ r → s < r ^ 2 → ∀ (c d : Weights),
    (∀ p ∈ Nat.primesLE (compactHeight r s),
      ∀ j ∈ Finset.Ico 1 (Nat.log p s + 1), c p j + d p j ≤ C) →
      R.readout false (r, s, C) (c, d) * R.readout true (r, s, C) (c, d) ∣
        compactExcess r s ^ C

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  have hh := h (r := 2) (s := 0) (C := 1) (by decide) (by decide)
    (fun _ _ => 0) (fun _ _ => 0)
    (by simp)
  cases role <;>
    change 0 ∣ compactExcess 2 0 ^ 1 at hh <;>
    exact (by decide : ¬ 0 ∣ compactExcess 2 0 ^ 1) hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  · refine ⟨(3, 8, 1), ((fun _ _ => 0), (fun _ _ => 0)),
      ((fun _ _ => 1), (fun _ _ => 0)), ?_⟩
    simpa only [actual, realize, Bool.false_eq_true, ite_false, ite_true] using excess_separation
  · refine ⟨(3, 8, 1), ((fun _ _ => 0), (fun _ _ => 0)),
      ((fun _ _ => 0), (fun _ _ => 1)), ?_⟩
    simpa only [actual, realize, Bool.false_eq_true, ite_false, ite_true] using excess_separation

def family : Registration arena (type_of% @actual_weighted_shared_budget) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_weighted_shared_budget, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected role, ?_, rfl, rejected_law role⟩
      intro i hi
      funext z w
      simp [actual, rejected, realize, hi]
    · intro e
      exact nomatch e
  dependence := dependence
end Shared

def sharedAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_weighted_shared_budget) (Realization Shared.signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Weighted.CompactBudget.actual_weighted_shared_budget.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompactBudget.Shared.family
  realizationSource := none
  generated := false
  arena := .source ⟨Shared.arena⟩
  objectArena := .source ⟨Shared.arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source Shared.arena ⟨Shared.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Shared.signature
    (fun role z w => compactWeightedExcess z.1 z.2.1 (if role then w.2 else w.1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Weighted.CompactBudget
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body",
          "fn", "arg", "fn", "arg"]
        stateBinder := 5
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body",
          "fn", "arg", "arg"]
        stateBinder := 6
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Bounded
abbrev signature : Signature where
  Params := ℕ × ℕ × ℕ
  State _ := Weights
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z c => compactWeightedExcess z.1 z.2.1 c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r s C : ℕ}, 2 ≤ r → s < r ^ 2 → ∀ (c : Weights),
    (∀ p ∈ Nat.primesLE (compactHeight r s),
      ∀ j ∈ Finset.Ico 1 (Nat.log p s + 1), c p j ≤ C) →
      R.readout () (r, s, C) c ∣ compactExcess r s ^ C

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 2) (s := 0) (C := 1) (by decide) (by decide)
    (fun _ _ => 0) (by simp)
  change 0 ∣ compactExcess 2 0 ^ 1 at hh
  exact (by decide : ¬ 0 ∣ compactExcess 2 0 ^ 1) hh

def family : Registration arena (type_of% @actual_weighted_budget) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_weighted_budget, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨(3, 8, 1), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
    simpa only [actual, realize] using excess_separation
end Bounded

def boundedAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_weighted_budget) (Realization Bounded.signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.Weighted.CompactBudget.actual_weighted_budget.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompactBudget.Bounded.family
  realizationSource := none
  generated := false
  arena := .source ⟨Bounded.arena⟩
  objectArena := .source ⟨Bounded.arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source Bounded.arena ⟨Bounded.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Bounded.signature
    (fun _ z c => compactWeightedExcess z.1 z.2.1 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Weighted.CompactBudget
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.Weighted.CompactBudget
