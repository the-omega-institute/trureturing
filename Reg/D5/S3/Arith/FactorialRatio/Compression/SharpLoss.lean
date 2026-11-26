import D5.S3.Arith.FactorialRatio.Compression.SharpLoss
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The primewise loss and the two weighted losses are readouts on whole
families of compact parameters and prime-power weights. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.FactorialRatio.Compression.SharpLoss

open _root_.D5.S3.Arith.FactorialRatio.Compression.SharpLoss
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private theorem prime_loss_separates :
    (compactExcess 3 5).factorization 5 ≠ (compactExcess 3 7).factorization 5 := by
  have hsmall : compactExcess 3 5 = 2 := by decide
  have hlarge : compactExcess 3 7 = 15 := by decide
  rw [hsmall, hlarge, Nat.factorization_eq_zero_of_lt (by decide : 2 < 5)]
  have hpos : 0 < (15 : ℕ).factorization 5 :=
    Nat.Prime.factorization_pos_of_dvd (by decide : Nat.Prime 5)
      (by decide : (15 : ℕ) ≠ 0) (by decide : (5 : ℕ) ∣ 15)
  exact (ne_of_gt hpos).symm

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
  norm_num [arena, rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(3, 5, 1), 5, 7, ?_⟩
  exact prime_loss_separates

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
    coordinates := #[0, 2, 3]
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

namespace Factorization

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z s => (compactExcess z.1 s).factorization z.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1000) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r s p : ℕ), 2 ≤ r → s < r ^ 2 →
    R.readout () (r, p) s =
      (D5.S3.Arith.FactorialRatio.CompactFactorialGcd.selbergGcd r s).factorization p -
        (D5.S3.Arith.FactorialRatio.RankOneLCMGcd.tailLCM
          (r * s + r - 1) (r - 1)).factorization p

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 0 2 (by decide) (by decide)
  have hG : D5.S3.Arith.FactorialRatio.CompactFactorialGcd.selbergGcd 2 0 = 1 := by decide
  have hT : D5.S3.Arith.FactorialRatio.RankOneLCMGcd.tailLCM
      (2 * 0 + 2 - 1) (2 - 1) = 1 := by decide
  norm_num [arena, rejected, realize, hG, hT] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(3, 5), 5, 7, ?_⟩
  exact prime_loss_separates

def family : Registration arena (type_of% @compactExcess_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@compactExcess_factorization, rejected, rejected_law⟩
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

end Factorization

def factorizationAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@compactExcess_factorization) (Realization Factorization.signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.SharpLoss.compactExcess_factorization.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.SharpLoss.Factorization.family
  realizationSource := none
  generated := false
  arena := .source ⟨Factorization.arena⟩
  objectArena := .source ⟨Factorization.arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source Factorization.arena ⟨Factorization.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Factorization.signature
    (fun _ z s => (compactExcess z.1 s).factorization z.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.SharpLoss
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
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
    coordinates := #[0, 1, 2, 5]
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

namespace MinimumLower

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z f => minimum z.1 z.2 f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r s b : ℕ} (f : ℕ → ℕ), b ∈ legalParameters r s →
    R.readout () (r, s) f ≤ f b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 1) (s := 0) (b := 0) (fun _ => 0) (by decide)
  change 1 ≤ 0 at hh
  exact (by decide : ¬ (1 : ℕ) ≤ 0) hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(1, 0), (fun _ => 0), (fun _ => 1), ?_⟩
  change minimum 1 0 (fun _ => 0) ≠ minimum 1 0 (fun _ => 1)
  decide

def family : Registration arena (type_of% @minimum_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minimum_le, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@minimum_le) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.FactorialRatio.Compression.SharpLoss.minimum_le.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.SharpLoss.MinimumLower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ z f => minimum z.1 z.2 f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.SharpLoss
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinimumLower

namespace MinimumAttained

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z f => minimum z.1 z.2 f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r s : ℕ) (f : ℕ → ℕ),
    ∃ b ∈ legalParameters r s, f b = R.readout () (r, s) f

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨b, hb, hh⟩ := h 1 0 (fun _ => 0)
  change 0 = 1 at hh
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(1, 0), (fun _ => 0), (fun _ => 1), ?_⟩
  change minimum 1 0 (fun _ => 0) ≠ minimum 1 0 (fun _ => 1)
  decide

def family : Registration arena (type_of% @minimum_attained) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minimum_attained, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@minimum_attained) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.FactorialRatio.Compression.SharpLoss.minimum_attained.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.SharpLoss.MinimumAttained.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ z f => minimum z.1 z.2 f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.SharpLoss
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinimumAttained

end Reg.D5.S3.Arith.FactorialRatio.Compression.SharpLoss
