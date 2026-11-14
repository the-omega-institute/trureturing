import D5.S3.Arith.Robin.PriceRecord.ActualRecordElementarySingleTwoTail
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- The literal source bridge and actual observational dependence are retained.
Whole-family variation, sensitivity and lawful template binding are unresolved.
No complete four-slot registration or declared_validated status is asserted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordElementarySingleTwoTail

open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap (ownPrice)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization (FullRecord)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace eventual_actual_record_single_two_tail

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => m.factorization 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
    V.readout () () m ≤ optimalLayerCount (ownPrice m) 2 + 1

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordElementarySingleTwoTail.eventual_actual_record_single_two_tail

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordElementarySingleTwoTail.eventual_actual_record_single_two_tail)) ↔
      arena.Law actual := Iff.rfl

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Nat.factorization 1 2 ≠ Nat.factorization 2 2
  norm_num [Nat.Prime.factorization_self Nat.prime_two]

private theorem variation_requires_unbounded_records (h : Variation arena actual) :
    ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ ∃ mu : ℝ, 0 < mu ∧ FullRecord m mu := by
  intro M
  by_contra hnone
  obtain ⟨_hlaw, bad, hbad⟩ := h
  apply hbad
  refine ⟨M, ?_⟩
  intro m hm mu hmu hrecord
  exact (hnone ⟨m, hm, mu, hmu, hrecord⟩).elim

end eventual_actual_record_single_two_tail

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordElementarySingleTwoTail
