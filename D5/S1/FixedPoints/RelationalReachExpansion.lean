/- GID: D5/S1/FixedPoints/RelationalReachExpansion
   generality: G
   mirror-B: D5/B/S1/FixedPoints/RelationalReachExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relational reachability is the union of its finite least-fixed-point stages. -/

import D5.S1.FixedPoints.KleeneStageLimit
import Mathlib.Data.Rel

/- Library-search audit trail (2026-08-20):
   * Exact pinned-Mathlib hit: `SetRel.image_iUnion` states that relation
     direct image preserves arbitrary indexed unions; it is applied below.
   * Exact repository hit:
     `inductive_definition_is_supremum_of_stages` directly wraps Mathlib's
     Kleene least-fixed-point theorem; it is applied after continuity is
     derived for the source's relation-generated operator.
   * Repository searches found no theorem already constructing this operator
     from a transition relation and initial set. -/

namespace D5.S1.FixedPoints.RelationalReachExpansion

open OmegaCompletePartialOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- One reachability step keeps every initial state and adds the direct
relational image of the current approximation. -/
def reachStep {X : Type*} (relation : SetRel X X) (initial : Set X) :
    Set X →o Set X where
  toFun current := initial ∪ relation.image current
  monotone' := by
    intro current later hlater state hstate
    rcases hstate with hstate | hstate
    · exact Or.inl hstate
    · exact Or.inr (SetRel.image_mono hlater hstate)

private theorem omegaSup_sets_eq_iUnion {X : Type*}
    (chain : Chain (Set X)) :
    ωSup chain = ⋃ n, chain n := by
  apply le_antisymm
  · exact (ωSup_le_iff).2 fun n => Set.subset_iUnion (fun m => chain m) n
  · exact Set.iUnion_subset fun n => le_ωSup chain n

private theorem reachStep_omegaScottContinuous {X : Type*}
    (relation : SetRel X X) (initial : Set X) :
    ωScottContinuous (reachStep relation initial) := by
  apply ωScottContinuous.of_map_ωSup_of_orderHom
  intro chain
  rw [omegaSup_sets_eq_iUnion chain,
    omegaSup_sets_eq_iUnion (chain.map (reachStep relation initial))]
  change
    initial ∪ relation.image (⋃ n, chain n) =
      ⋃ n, (initial ∪ relation.image (chain n))
  rw [SetRel.image_iUnion]
  ext state
  simp only [Set.mem_union, Set.mem_iUnion, SetRel.mem_image]
  constructor
  · rintro (hinitial | ⟨n, prior, hprior, hrelation⟩)
    · exact ⟨0, Or.inl hinitial⟩
    · exact ⟨n, Or.inr ⟨prior, hprior, hrelation⟩⟩
  · rintro ⟨n, hinitial | ⟨prior, hprior, hrelation⟩⟩
    · exact Or.inl hinitial
    · exact Or.inr ⟨n, prior, hprior, hrelation⟩

/-- Relation direct image preserves every indexed union, and therefore the
least fixed point of the reachability operator is exactly the union of its
finite iterates from the empty set. -/
theorem finite_step_expansion
    {X Index : Type*} (relation : SetRel X X) (initial : Set X)
    (family : Index → Set X) :
    relation.image (⋃ i, family i) = ⋃ i, relation.image (family i) ∧
      (reachStep relation initial).lfp =
        ⋃ n : ℕ, (reachStep relation initial)^[n] ∅ := by
  constructor
  · exact SetRel.image_iUnion relation family
  · simpa only [Set.iSup_eq_iUnion, Set.bot_eq_empty] using
      D5.S1.FixedPoints.KleeneStageLimit.inductive_definition_is_supremum_of_stages
        (reachStep relation initial)
        (reachStep_omegaScottContinuous relation initial)

/-- The state domain used by the concrete source-data witness is inhabited. -/
example : Bool := false

/-- A one-edge relation and a singleton initial set witness the public
relation, initial-set, and indexed-family data. -/
example : SetRel Bool Bool × Set Bool × (Fin 2 → Set Bool) :=
  ({(false, true)}, {false}, fun i => if i = 0 then {false} else {true})

#print axioms finite_step_expansion

end D5.S1.FixedPoints.RelationalReachExpansion
