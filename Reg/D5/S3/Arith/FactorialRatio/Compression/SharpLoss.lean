import D5.S3.Arith.FactorialRatio.Compression.SharpLoss
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The primewise loss and the two weighted losses are readouts on whole
families of compact parameters and prime-power weights. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.Compression.SharpLoss

open _root_.D5.S3.Arith.FactorialRatio.Compression.SharpLoss
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Local

abbrev signature : Signature where
  Params := ℕ × ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z s => (compactExcess z.1 s).factorization z.2.1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1000) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r s p k : ℕ), 2 ≤ r → s < r ^ 2 → p.Prime → r < p →
    k * p ≤ s → 1 ≤ k →
      (R.readout () (r, p, k) s : ℝ) ≤
        2 * (k : ℝ) + 2 * (r : ℝ) ^ 2 / ((k : ℝ) * p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 3 8 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  change (1000 : ℝ) ≤ 2 * 1 + 2 * 3 ^ 2 / (1 * 5) at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(3, 2, 1), 0, 8, ?_⟩
  change (compactExcess 3 0).factorization 2 ≠ (compactExcess 3 8).factorization 2
  decide

def family : Registration arena (type_of% @local_prime_excess_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@local_prime_excess_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro i hi
      cases role
      cases i
      exact (hi rfl).elim
    · intro e
      exact nomatch e
  dependence := dependence

end Local

def localAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@local_prime_excess_bound) (Realization Local.signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.SharpLoss.local_prime_excess_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.SharpLoss.Local.family
  realizationSource := none
  generated := false
  arena := .source ⟨Local.arena⟩
  objectArena := .source ⟨Local.arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source Local.arena ⟨Local.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Local.signature
    (fun _ z s => (compactExcess z.1 s).factorization z.2.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.SharpLoss
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Shared

abbrev Weights := ℕ → ℕ → ℕ
abbrev Parameters := ℕ × ℕ × ℕ × Finset ℕ

abbrev signature : Signature where
  Params := Parameters
  State _ := Weights × Weights
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun role z w => weightedExcess z.1 z.2.1 z.2.2.2 (if role then w.2 else w.1))
    (fun e => nomatch e)

def rejected (role : Bool) : Realization signature :=
  realize signature
    (fun i z w => if i = role then 0 else
      weightedExcess z.1 z.2.1 z.2.2.2 (if i then w.2 else w.1))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r s C : ℕ), 2 ≤ r → s < r ^ 2 →
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ (c d : Weights),
      (∀ p ∈ P, ∀ j ∈ Finset.Ico 1 (Nat.log p s + 1), c p j + d p j ≤ C) →
      R.readout false (r, s, C, P) (c, d) * R.readout true (r, s, C, P) (c, d) ∣
        compactExcess r s ^ C

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  have hh := h 2 0 1 (by decide) (by decide) ∅ (by simp)
    (fun _ _ => 0) (fun _ _ => 0) (by simp)
  cases role <;>
    change 0 ∣ compactExcess 2 0 ^ 1 at hh <;>
    exact (by decide : ¬ 0 ∣ compactExcess 2 0 ^ 1) hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(3, 8, 1, {2}), ((fun _ _ => 0), (fun _ _ => 0)),
    ((fun _ _ => 1), (fun _ _ => 1)), ?_⟩
  cases role <;>
    change weightedExcess 3 8 {2} (fun _ _ => 0) ≠
      weightedExcess 3 8 {2} (fun _ _ => 1) <;>
    decide

def family : Registration arena (type_of% @weighted_shared_budget) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_shared_budget, rejected false, rejected_law false⟩
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
    (@weighted_shared_budget) (Realization Shared.signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.SharpLoss.weighted_shared_budget.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.SharpLoss.Shared.family
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
    (fun role z w => weightedExcess z.1 z.2.1 z.2.2.2 (if role then w.2 else w.1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.SharpLoss
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
          "fn", "arg", "fn", "arg"]
        stateBinder := 7
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
          "fn", "arg", "arg"]
        stateBinder := 8
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.Compression.SharpLoss
