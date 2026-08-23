/- GID: D5/S3/ConceptDynamics/Aggregation/MajorityCycleNotScalarOrder
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Aggregation/MajorityCycleNotScalarOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A concrete three-voter majority cycle has no faithful scalar ordering. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'majority_cycle_not_scalar_order' D5 Golden/Frozen/accepted`
     returned no matches.
   * `rg -n 'condorcet|majority|cycle|aggregation' D5/ --glob '*.lean'` found only
     unrelated uses of cycles and one majority module,
     `InstitutionalCapture.ByzantineMajorityRecovery`. Reading it confirmed that it
     recovers a Boolean truth from Byzantine reports rather than aggregating rankings.
   * Pinned-Mathlib searches for `condorcet`, `majorityPrefers`, `pairwise majority`,
     and `majority.*cycle` returned no matches. The proof therefore uses finite
     computation for the three ballots and the basic order lemmas `lt_trans` and
     `lt_asymm`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder

/-- The rank assigned by voter `v` to candidate `x`. Lower ranks are preferred.
For voters `0`, `1`, and `2`, this encodes `a>b>c`, `b>c>a`, and `c>a>b`. -/
def preferenceRank (v x : Fin 3) : Nat :=
  (x.val + (3 - v.val)) % 3

/-- Voter `v` strictly prefers `x` to `y` when `x` has lower rank. -/
def prefers (v x y : Fin 3) : Prop :=
  preferenceRank v x < preferenceRank v y

instance decidablePrefers (v x y : Fin 3) : Decidable (prefers v x y) := by
  unfold prefers
  infer_instance

/-- Candidate `x` beats `y` when at least two of the three voters prefer `x`. -/
def majorityPrefers (x y : Fin 3) : Prop :=
  2 ≤ (Finset.univ.filter fun v => prefers v x y).card

instance decidableMajorityPrefers (x y : Fin 3) : Decidable (majorityPrefers x y) := by
  unfold majorityPrefers
  infer_instance

/-- A directed three-cycle cannot be faithfully represented in any linear order. -/
theorem three_cycle_not_scalar_order {Candidate Utility : Type*} [LinearOrder Utility]
    (relation : Candidate → Candidate → Prop) (a b c : Candidate)
    (hab : relation a b) (hbc : relation b c) (hca : relation c a) :
    ¬ ∃ u : Candidate → Utility, ∀ x y, relation x y → u x > u y := by
  rintro ⟨u, represents⟩
  have uab : u b < u a := represents a b hab
  have ubc : u c < u b := represents b c hbc
  have uca : u a < u c := represents c a hca
  exact (lt_asymm (lt_trans ubc uab) uca)

/-- In the concrete profile, every edge of the Condorcet cycle wins by exactly two
votes to one. -/
theorem condorcet_cycle_vote_counts :
    (Finset.univ.filter fun v => prefers v 0 1).card = 2 ∧
      (Finset.univ.filter fun v => prefers v 1 2).card = 2 ∧
        (Finset.univ.filter fun v => prefers v 2 0).card = 2 := by
  decide

/-- The displayed three-voter Condorcet profile produces a majority cycle, so its
majority relation has no faithful representation in any scalar linear order. -/
theorem majority_cycle_not_scalar_order {Utility : Type*} [LinearOrder Utility] :
    ¬ ∃ u : Fin 3 → Utility, ∀ x y, majorityPrefers x y → u x > u y := by
  rcases condorcet_cycle_vote_counts with ⟨hab, hbc, hca⟩
  apply three_cycle_not_scalar_order majorityPrefers 0 1 2
  · rw [majorityPrefers, hab]
  · rw [majorityPrefers, hbc]
  · rw [majorityPrefers, hca]

example : majorityPrefers 0 1 ∧ majorityPrefers 1 2 ∧ majorityPrefers 2 0 := by
  exact ⟨by decide, by decide, by decide⟩

#print axioms majority_cycle_not_scalar_order

end D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder
