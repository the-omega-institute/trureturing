/- GID: D5/S3/ConceptDynamics/Policy/DeterministicPolicySectionCount
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Policy/DeterministicPolicySectionCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct public states with at least two legal actions force an exponential family of deterministic sections. -/

import Mathlib

/- Library-search audit trail (2026-08-27):
   * Exact repository and pinned-Mathlib searches found no theorem packaging the
     lower bound for legal-action section spaces.
   * The proof applies `Fintype.card_pi`, `Finset.prod_image`,
     `Finset.prod_le_pow_card` in the order-dual form, and
     `Finset.prod_le_prod_of_subset_of_one_le'` directly.
   * The public section carrier is the source-constructed dependent product
     `∀ q, {a // a ∈ legal q}`; no target-shaped section predicate is defined.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Policy.DeterministicPolicySectionCount

open scoped BigOperators

/-- If `k` distinct public states have at least two legal actions each, the
space of deterministic legal sections has cardinality at least `2^k`. -/
theorem deterministic_policy_sections_lower_bound
    {Q A : Type*}
    (legal : Q → Set A)
    (finiteQ : Finite Q) (finiteA : Finite A)
    (legal_nonempty : ∀ q, (legal q).Nonempty)
    {k : Nat} (selected : Fin k → Q)
    (selected_injective : Function.Injective selected)
    (fiber_large : ∀ i, 2 ≤ Nat.card {a : A // a ∈ legal (selected i)}) :
    2 ^ k ≤ Nat.card (∀ q, {a : A // a ∈ legal q}) := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fintype A := Fintype.ofFinite A
  letI : ∀ q, Fintype {a : A // a ∈ legal q} := fun q => Fintype.ofFinite _
  let fiberCard : Q → Nat := fun q => Fintype.card {a : A // a ∈ legal q}
  have hselected : 2 ^ k ≤ ∏ i : Fin k, fiberCard (selected i) := by
    have hprod := Finset.pow_card_le_prod
      (Finset.univ : Finset (Fin k)) (fun i => fiberCard (selected i)) 2 (by
        intro i hi
        simpa [fiberCard, Nat.card_eq_fintype_card] using fiber_large i)
    simpa [fiberCard] using hprod
  have himage :
      (∏ q ∈ (Finset.univ.image selected), fiberCard q) =
        ∏ i ∈ (Finset.univ : Finset (Fin k)), fiberCard (selected i) := by
    exact Finset.prod_image selected_injective.injOn
  have htotal :
      (∏ q ∈ (Finset.univ.image selected), fiberCard q) ≤
        ∏ q ∈ (Finset.univ : Finset Q), fiberCard q := by
    apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.subset_univ _)
    intro q hq hnot
    have hpos : 0 < fiberCard q := by
      dsimp [fiberCard]
      apply Fintype.card_pos_iff.mpr
      obtain ⟨a, ha⟩ := legal_nonempty q
      exact ⟨⟨a, ha⟩⟩
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos)
  calc
    2 ^ k ≤ ∏ i : Fin k, fiberCard (selected i) := hselected
    _ = ∏ q ∈ (Finset.univ.image selected), fiberCard q := himage.symm
    _ ≤ ∏ q ∈ (Finset.univ : Finset Q), fiberCard q := htotal
    _ = Nat.card (∀ q, {a : A // a ∈ legal q}) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_pi]

#print axioms deterministic_policy_sections_lower_bound

end D5.S3.ConceptDynamics.Policy.DeterministicPolicySectionCount
