import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
import Reg.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
import D5.S3.ConceptDynamics.Attribution.ParityStackedRankBounds
import Reg.Support.DependentFamily

/-! Dependence of the joint lower bound on the chosen row and column thresholds. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
open _root_.D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
open _root_.D5.S3.ConceptDynamics.Attribution.ParityStackedRankBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := Finset ℕ × Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def bound (p : Σ _ : ℕ, ℕ) (cuts : Finset ℕ × Finset ℕ) : ℕ :=
  (∑ r ∈ cuts.1, ((highOrdinaryEvenRanks (n := p.1) r).card + 1 -
    p.2 * (lowOddRanks (n := p.1) r).card)) +
    (∑ r ∈ cuts.2, ((highOdd (n := p.1) r).card + 1 - p.2 * ((lowEven (n := p.1) r).card + 1)))

def actual : Realization signature :=
  realize signature (fun _ p t => bound p t) (fun e => nomatch e)

def raised : Realization signature :=
  realize signature (fun _ _ _ => 6145) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ) (even : n % 2 = 0) (_ : k % 2 = 1)
    (cuts : Finset ℕ × Finset ℕ), Disjoint cuts.1 cuts.2 →
    ∀ (mass : EvenSubset n → OddSubset n → ℕ) (flags : OddSubset n → ℕ),
    (∀ p, ∑ q, mass p q = k) → (∀ q, ∑ p, mass p q = k) →
    ∀ (q : OddSubset n), 1 ≤ mass ⟨univ, by simpa using even⟩ q →
    (∑ c, flags c * c.val.card) + R.readout () ⟨n,k⟩ cuts ≤
      (∑ p : EvenSubset n, ∑ c : OddSubset n,
        (if p = ⟨univ, by simpa using even⟩ then flags c else mass p c % 2) *
          (p.val ∩ c.val).card) +
      ((∑ r ∈ cuts.1, (if q ∈ highOdd r then
          let d := (highOrdinaryEvenRanks (n := n) r).card + 1 - k * (lowOddRanks (n := n) r).card
          d - (d - 1) else 0 : ℕ)) +
       (∑ r ∈ cuts.2, (if q ∈ highOdd r then
          let d := (highOdd (n := n) r).card + 1 - k * ((lowEven (n := n) r).card + 1)
          d - (d - 1) else 0 : ℕ)))

private theorem raised_fails : ¬ arena.Law raised := by
  intro law
  obtain ⟨mass, rows, cols, one⟩ := rank_test_matrix
  let full : EvenSubset 6 := ⟨univ, by decide⟩
  have positive : ∃ q, 1 ≤ mass full q := by
    by_contra! h
    have zero (q : OddSubset 6) : mass full q = 0 := by
      have small := h q
      omega
    simpa [zero] using rows full
  obtain ⟨q, hq⟩ := positive
  have impossible := law 6 1 (by decide) (by decide) (∅, ∅) (by simp)
    mass (mass full) rows cols q hq
  have same :
      (∑ p : EvenSubset 6, ∑ q : OddSubset 6,
        (if p = full then mass full q else mass p q % 2) * (p.val ∩ q.val).card) =
      ∑ p : EvenSubset 6, ∑ q : OddSubset 6,
        (if p.val = univ then mass full q else mass p q % 2) * (p.val ∩ q.val).card := by
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    by_cases h : p = full
    · subst p
      rw [ite_eq_left rfl, ite_eq_left (show full.val = univ from rfl)]
    · rw [ite_eq_right h, ite_eq_right (fun eq => h (Subtype.ext eq))]
  have claimed : 6145 ≤ ∑ p : EvenSubset 6, ∑ c : OddSubset 6,
      (if p = full then mass full c else mass p c % 2) * (p.val ∩ c.val).card := by
    change (∑ c, mass full c * c.val.card) + 6145 ≤
      (∑ p : EvenSubset 6, ∑ c : OddSubset 6,
        (if p = full then mass full c else mass p c % 2) * (p.val ∩ c.val).card) +
      ((∑ r ∈ (∅ : Finset ℕ), (if q ∈ highOdd r then
          let d := (highOrdinaryEvenRanks (n := 6) r).card + 1 - 1 * (lowOddRanks (n := 6) r).card
          d - (d - 1) else 0 : ℕ)) +
       (∑ r ∈ (∅ : Finset ℕ), (if q ∈ highOdd r then
          let d := (highOdd (n := 6) r).card + 1 - 1 * ((lowEven (n := 6) r).card + 1)
          d - (d - 1) else 0 : ℕ))) at impossible
    simp only [sum_empty, Nat.add_zero] at impossible
    omega
  have upper := test_score_at_most mass (mass full) one (one full)
  exact (by decide : ¬ 6145 ≤ 6144) (claimed.trans (same.le.trans upper))


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
    exact ⟨⟨6,1⟩, (∅, ∅), (∅, {2}), by decide +kernel⟩

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
  readout := some (realize signature (fun _ p t => bound p t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
