import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
import Reg.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
import D5.S3.ConceptDynamics.Attribution.ParityStackedRankBounds
import Reg.Support.DependentFamily

/-! Dependence of the exact rank deficits on the table and the chosen thresholds. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
open _root_.D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State := RankCutTable
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ table => cutDeficitSum table) (fun e => nomatch e)

def raised : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (table : RankCutTable n), table.1.val.card = n →
    (∀ p, (∑ q, table.2.1 p q) % 2 = 1) →
    (∀ q, (∑ p, table.2.1 p q) % 2 = 1) →
    R.readout () n table ≤
    ∑ p : EvenSubset n, ∑ q : OddSubset n,
      if p = table.1 then 0
      else (table.2.1 p q % 2) *
        (∑ r ∈ (table.2.2.1 ∪ table.2.2.2) ∩ Ioc (n - q.val.card) p.val.card,
          let d := mixedDeficit table.1 table.2.1 table.2.2 r
          d - (d - 1))

private theorem raised_fails : ¬ arena.Law raised := by
  intro law
  obtain ⟨mass, rows, cols, _⟩ := rank_test_matrix
  let full : EvenSubset 6 := ⟨univ, by decide⟩
  have fullSize : full.val.card = 6 := by simp [full]
  have h := law 6 (full, mass, ∅, ∅) fullSize
    (fun p => by rw [rows]) (fun q => by rw [cols])
  simp only [raised, realize, empty_union, empty_inter, sum_empty, Nat.mul_zero,
    ite_self, sum_const_zero] at h
  exact (by decide : ¬ (1 : ℕ) ≤ 0) h

def family : Registration arena (type_of% mixed_rank_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mixed_rank_lower, raised, raised_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨raised, ?_, rfl, raised_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    let full : EvenSubset 2 := ⟨univ, by decide⟩
    exact ⟨2, (full, fun _ _ => 0, ∅, ∅), (full, fun _ _ => 0, {0}, ∅),
      by decide +kernel⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    mixed_rank_lower (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds.rankThresholds
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ table => cutDeficitSum table) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
