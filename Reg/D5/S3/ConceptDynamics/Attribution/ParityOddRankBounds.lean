import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
import Reg.Support.DependentFamily

/-! Dependence of the rank bound on the odd marginal multiplier. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

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

def actual : Realization signature :=
  realize signature (fun _ n k => 1 + (n + 1 - 2 * k) + (n.choose 2 + 1 - n * k))
    (fun e => nomatch e)

def raisedBound : Realization signature :=
  realize signature (fun _ n _ => (2 ^ n) * (2 ^ n) * n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ) (_ : 6 ≤ n) (even : n % 2 = 0) (_ : k % 2 = 1)
    (mass : EvenSubset n → OddSubset n → ℕ) (flags : OddSubset n → ℕ),
    (∀ p, ∑ q, mass p q = k) → (∀ q, ∑ p, mass p q = k) →
    (∀ q, flags q ≤ mass ⟨univ, by simpa using even⟩ q) →
    (∃ q, 0 < flags q) →
    R.readout () n k ≤ ∑ p : EvenSubset n, ∑ q : OddSubset n,
      (if p.val = univ then flags q else mass p q % 2) * (p.val ∩ q.val).card

private theorem rank_test_matrix :
    ∃ m : EvenSubset 6 → OddSubset 6 → ℕ, (∀ p, ∑ q, m p q = 1) ∧
      (∀ q, ∑ p, m p q = 1) ∧ ∀ p q, m p q ≤ 1 := by
  classical
  have evenCard : Fintype.card (EvenSubset 6) = 32 := by decide
  have oddCard : Fintype.card (OddSubset 6) = 32 := by decide
  let pairing : EvenSubset 6 ≃ OddSubset 6 := Fintype.equivOfCardEq (evenCard.trans oddCard.symm)
  let m (p : EvenSubset 6) (q : OddSubset 6) := if pairing p = q then (1 : ℕ) else 0
  refine ⟨m, ?_, ?_, ?_⟩
  · intro p
    simp [m, eq_comm]
  · intro q
    have eq (p : EvenSubset 6) : pairing p = q ↔ p = pairing.symm q :=
      pairing.eq_symm_apply.symm
    simp [m, eq]
  · intro p q
    unfold m
    split <;> decide

private theorem test_score_at_most
    (m : EvenSubset 6 → OddSubset 6 → ℕ) (flags : OddSubset 6 → ℕ)
    (massBound : ∀ p q, m p q ≤ 1) (flagBound : ∀ q, flags q ≤ 1) :
    (∑ p : EvenSubset 6, ∑ q : OddSubset 6,
      (if p.val = univ then flags q else m p q % 2) * (p.val ∩ q.val).card) ≤ 6144 := by
  have localBound (p : EvenSubset 6) (q : OddSubset 6) :
      (if p.val = univ then flags q else m p q % 2) * (p.val ∩ q.val).card ≤ 6 := by
    have weightBound : (if p.val = univ then flags q else m p q % 2) ≤ 1 := by
      split
      · exact flagBound q
      · exact (Nat.mod_le _ _).trans (massBound p q)
    have size : (p.val ∩ q.val).card ≤ 6 := by
      simpa using card_le_card (subset_univ (p.val ∩ q.val))
    exact (Nat.mul_le_mul weightBound size).trans (by decide)
  have totalBound := sum_le_sum (s := (univ : Finset (EvenSubset 6)))
    fun p _ => sum_le_sum (s := (univ : Finset (OddSubset 6))) fun q _ => localBound p q
  have evenCard : Fintype.card (EvenSubset 6) = 32 := by decide
  have oddCard : Fintype.card (OddSubset 6) = 32 := by decide
  simp only [sum_const, card_univ, nsmul_eq_mul, evenCard, oddCard, Nat.cast_id] at totalBound
  exact totalBound.trans (by decide)

private theorem raised_bound_fails : ¬ arena.Law raisedBound := by
  intro law
  obtain ⟨m, row, col, massBound⟩ := rank_test_matrix
  let full : EvenSubset 6 := ⟨univ, by decide⟩
  have some : ∃ q, 0 < m full q := by
    by_contra! allZero
    have empty : ∀ q, m full q = 0 := fun q => Nat.eq_zero_of_le_zero (allZero q)
    have original := row full
    simp [empty] at original
  have claimed := law 6 1 (by decide) (by decide) (by decide) m (m full) row col
    (fun _ => le_rfl) some
  have upper := test_score_at_most m _ massBound (massBound full)
  exact (by decide : ¬ 24577 ≤ 6144) (claimed.trans upper)

def family : Registration arena (type_of% fixed_from_odd_margins) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fixed_from_odd_margins, raisedBound, raised_bound_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨raisedBound, ?_, rfl, raised_bound_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    exact ⟨6, 1, 3, by decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    fixed_from_odd_margins (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds.rankDeficits
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => 1 + (n + 1 - 2 * k) +
    (n.choose 2 + 1 - n * k)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev flagSignature : Signature where
  Params := ℕ
  State n := OddSubset n → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def flagCost : Realization flagSignature :=
  realize flagSignature (fun _ _ b => ∑ q, b q * q.val.card) (fun e => nomatch e)

def raisedFlagCost : Realization flagSignature :=
  realize flagSignature (fun _ _ _ => 6145) (fun e => nomatch e)

abbrev flagArena : Arena where
  signature := flagSignature
  Law R := ∀ (n k : ℕ) (_ : 6 ≤ n) (even : n % 2 = 0) (_ : k % 2 = 1)
    (mass : EvenSubset n → OddSubset n → ℕ) (flags : OddSubset n → ℕ),
    (∀ p, ∑ q, mass p q = k) → (∀ q, ∑ p, mass p q = k) →
    let full : EvenSubset n := ⟨univ, by simpa using even⟩
    R.readout () n flags +
      (n + (∑ q ∈ univ.filter (fun q : OddSubset n => q.val.card ≠ n - 1), mass full q)
        - 2 * k) +
      (n.choose 2 + (∑ q ∈ univ.filter (fun q : OddSubset n => q.val.card = 1), mass full q)
        - n * k) ≤
      ∑ p : EvenSubset n, ∑ q : OddSubset n,
        (if p.val = univ then flags q else mass p q % 2) * (p.val ∩ q.val).card

private theorem raised_flag_cost_fails : ¬ flagArena.Law raisedFlagCost := by
  intro law
  obtain ⟨m, row, col, massBound⟩ := rank_test_matrix
  have claimed := law 6 1 (by decide) (by decide) (by decide) m (fun _ => 0) row col
  have totalBound := test_score_at_most m (fun _ => 0) massBound (fun _ => by decide)
  dsimp [raisedFlagCost, realize] at claimed
  omega

def flagFamily : Registration flagArena (type_of% weighted_rank_deficits_le_intersections) where
  actual := flagCost
  bridge := Iff.rfl
  variation := ⟨weighted_rank_deficits_le_intersections, raisedFlagCost, raised_flag_cost_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨raisedFlagCost, ?_, rfl, raised_flag_cost_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    exact ⟨1, fun _ => 0, fun _ => 1, by decide⟩

def flagRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    weighted_rank_deficits_le_intersections (Realization flagSignature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds.fullRowFlagCost
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds.flagFamily
  realizationSource := none
  generated := false
  arena := .source ⟨flagArena⟩
  objectArena := .source ⟨flagArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source flagArena ⟨flagFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize flagSignature (fun _ _ b => ∑ q, b q * q.val.card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
