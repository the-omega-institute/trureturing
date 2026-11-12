import D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-law bridges retain the full original theorem telescopes.
The numerical tail readouts admit whole-family interventions. Source selection
and enrolled readout binding are separate obligations from these kernel proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap

open Finset
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenLocalThreshold
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.ActualGlobalBracketing
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace greatest_feasible_global_gap

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ s m C => GlobalBudgetGap s m C) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {s : ℝ} (hs : 0 < s) {m : ℕ}
    (hA : strictInteger s ≤ m) (hD : m ≤ maximalInteger s)
    (hnot : ¬ IsGoldenResourceOptimal s m),
    ∃ C : ℕ, V.readout () s m C

theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap.greatest_feasible_global_gap

theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap.greatest_feasible_global_gap)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end greatest_feasible_global_gap

namespace full_original2tail_deletion_identity

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c m => h2 m c) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m : ℕ} (hm : 1 ≤ m) {c : ℝ}
    (ha : optimalLayerCount c 2 ≤ m.factorization 2) (t : ℝ),
    1 ≤ deleted2tailInteger m c ∧
    (deleted2tailInteger m c).factorization 2 = optimalLayerCount c 2 ∧
    deleted2tailInteger m c * 2 ^ (m.factorization 2 - optimalLayerCount c 2) = m ∧
    goldenResourceObjective t m - goldenResourceObjective t (deleted2tailInteger m c) =
      (c - t) * V.readout () c m - J2 m c

theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap.full_original2tail_deletion_identity

theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap.full_original2tail_deletion_identity)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end full_original2tail_deletion_identity

namespace full_original2tail_reward_telescope

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c m => ordinary2tailReward m c) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m : ℕ} {c : ℝ}
    (ha : optimalLayerCount c 2 ≤ m.factorization 2),
    V.readout () c m =
      Real.log ((2 - (2 : ℝ)⁻¹ ^ (m.factorization 2)) /
        (2 - (2 : ℝ)⁻¹ ^ (optimalLayerCount c 2)))

theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap.full_original2tail_reward_telescope

theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap.full_original2tail_reward_telescope)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end full_original2tail_reward_telescope

namespace full_original2tail_reward_bound

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c m => ordinary2tailReward m c) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m : ℕ} {c : ℝ} (hc : 0 < c)
    (ha : optimalLayerCount c 2 ≤ m.factorization 2),
    V.readout () c m <
        2 * (goldenLayerMarginal 2 (optimalLayerCount c 2 + 1) * Real.log 2) ∧
      V.readout () c m < 2 * c * Real.log 2

theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap.full_original2tail_reward_bound

theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap.full_original2tail_reward_bound)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end full_original2tail_reward_bound

namespace full_original2tail_forbidden_budget

abbrev signature : Signature where
  Params := ℝ × ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ prices m C => FullTailBudgetRestriction prices.1 prices.2 m C) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m k : ℕ} (hm : 1 ≤ m)
    (hT : 1 < Real.log (m : ℝ)) {mu s : ℝ} (hmu : 0 < mu)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective mu n < goldenResourceObjective mu m)
    (hk : 1 ≤ k) (hkv : k ≤ m.factorization 2)
    (hbad : goldenLayerMarginal 2 k < ownPrice m)
    (hs : 0 < s) (hA : strictInteger s ≤ m) (hD : m ≤ maximalInteger s)
    (hsc : ownPrice m ≤ s),
    ∃ C : ℕ, GlobalBudgetGap s m C ∧ V.readout () (mu, s) m C

theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap.full_original2tail_forbidden_budget

theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap.full_original2tail_forbidden_budget)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end full_original2tail_forbidden_budget

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap
