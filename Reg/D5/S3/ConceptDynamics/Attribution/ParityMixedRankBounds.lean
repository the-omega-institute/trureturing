import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
import Reg.Support.DependentFamily

/-! Dependence of the exact rank deficits on the table and the chosen thresholds. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
open _root_.D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

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
  Law R := ∀ (n : ℕ) (table : RankCutTable n),
    (R.readout () n table ≤ ∑ p : EvenSubset n, ∑ q : OddSubset n,
      (table.2.1 p q % 2) * chargeCount table p q) ∧
    (∀ p q, chargeCount table p q ≤ intervalCap table p q) ∧
    (∀ p q, intervalCap table p q ≤ if p = table.1 then 0 else (p.val ∩ q.val).card) ∧
    (∃ allocated : EvenSubset n → OddSubset n → ℕ,
      (∑ p, ∑ q, allocated p q) = cutDeficitSum table ∧
      ∀ p q, allocated p q ≤ (table.2.1 p q % 2) * chargeCount table p q)

private theorem raised_fails : ¬ arena.Law raised := by
  intro law
  let full : EvenSubset 2 := ⟨univ, by decide⟩
  have h := (law 2 (full, fun _ _ => 0, ∅, ∅)).1
  change 1 ≤ (∑ p : EvenSubset 2, ∑ q : OddSubset 2, 0 % 2 * _) at h
  simp at h

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
    let full : EvenSubset 4 := ⟨univ, by decide⟩
    let p : EvenSubset 4 := ⟨{0, 1}, by decide⟩
    let q : OddSubset 4 := ⟨{0, 1, 2}, by decide⟩
    let mass : EvenSubset 4 → OddSubset 4 → ℕ :=
      fun x y => if x = p ∧ y = q then 1 else 0
    exact ⟨4, (full, mass, ∅, ∅), (full, mass, {2}, ∅), by decide +kernel⟩

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
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
