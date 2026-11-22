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

private theorem raised_bound_fails : ¬ arena.Law raisedBound := by
  classical
  intro law
  have evenCard : Fintype.card (EvenSubset 6) = 32 := by decide
  have oddCard : Fintype.card (OddSubset 6) = 32 := by decide
  let pairing : EvenSubset 6 ≃ OddSubset 6 := Fintype.equivOfCardEq (evenCard.trans oddCard.symm)
  let full : EvenSubset 6 := ⟨univ, by decide⟩
  let m (p : EvenSubset 6) (q : OddSubset 6) := if pairing p = q then (1 : ℕ) else 0
  have row (p : EvenSubset 6) : ∑ q, m p q = 1 := by
    simp [m, eq_comm]
  have col (q : OddSubset 6) : ∑ p, m p q = 1 := by
    have eq (p : EvenSubset 6) : pairing p = q ↔ p = pairing.symm q := pairing.apply_eq_iff_eq_symm_apply
    simp [m, eq]
  have claimed :=
    law 6 1 (by decide) (by decide) (by decide) m (m full) row col
      (fun _ => le_rfl) ⟨pairing full, by simp [m]⟩
  have localBound (p : EvenSubset 6) (q : OddSubset 6) :
      (if p.val = univ then m full q else m p q % 2) * (p.val ∩ q.val).card ≤ 6 := by
    have massBound (v : EvenSubset 6) : m v q ≤ 1 := by
      unfold m
      split <;> decide
    have flagBound : (if p.val = univ then m full q else m p q % 2) ≤ 1 := by
      split
      · exact massBound full
      · exact (Nat.mod_le _ _).trans (massBound p)
    have size : (p.val ∩ q.val).card ≤ 6 := by
      simpa using card_le_card (subset_univ (p.val ∩ q.val))
    exact (Nat.mul_le_mul flagBound size).trans (by decide)
  have totalBound := sum_le_sum (s := (univ : Finset (EvenSubset 6)))
    fun p _ => sum_le_sum (s := (univ : Finset (OddSubset 6))) fun q _ => localBound p q
  simp only [sum_const, card_univ, nsmul_eq_mul, evenCard, oddCard] at totalBound
  change 24577 ≤ _ at claimed
  omega

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

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
