import D5.S3.Arith.Robin.PriceRecord.ActualArbitraryBracketTwoTail
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The actual numerical readout and exact quantified source law are retained.
Whole-family intervention, sensitivity and lawful source selection remain
unregistered under https://github.com/the-omega-institute/trureturing/issues/29429.
No four-slot registration or declared_validated status is asserted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualArbitraryBracketTwoTail

open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m =>
    (2 : ℝ) ^ (m.factorization 2 - optimalLayerCount (ownPrice m) 2))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ K : ℝ, 4 < K → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ mu : ℝ, 0 < mu →
    (∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective mu n < goldenResourceObjective mu m) →
    V.readout () () m < K * Real.log (m : ℝ)

theorem actual_law : arena.Law actual := by
  exact _root_.D5.S3.Arith.Robin.PriceRecord.ActualArbitraryBracketTwoTail.full_original2tail_power_bound

theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualArbitraryBracketTwoTail.full_original2tail_power_bound)) ↔
      arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualArbitraryBracketTwoTail
