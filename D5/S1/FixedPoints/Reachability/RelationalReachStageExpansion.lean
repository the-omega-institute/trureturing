/- GID: D5/S1/FixedPoints/Reachability/RelationalReachStageExpansion
   generality: G
   mirror-B: D5/B/S1/FixedPoints/Reachability/RelationalReachStageExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relational reachability has explicit initial and successor stages. -/

import D5.S1.FixedPoints.RelationalReachExpansion

/- Library-search audit trail (2026-08-27):
   * Exact repository hit `finite_step_expansion` supplies arbitrary-union
     preservation and the least-fixed-point union; it is applied directly.
   * Exact pinned-Mathlib hits `Function.iterate_zero_apply`, `iterate_one`,
     and `Function.iterate_succ_apply'` supply the finite-stage identities.
   * Body-shape search for `initial union relation.image`, relation-image
     indexed unions, least-fixed-point stage unions, and one-step iterates
     found the canonical `reachStep` primitive and no complete public theorem
     already exposing the restored initial-stage clauses. -/

namespace D5.S1.FixedPoints.Reachability.RelationalReachStageExpansion

open D5.S1.FixedPoints.RelationalReachExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Relation direct image preserves arbitrary indexed unions. The constructed
reachability least fixed point is the union of its finite stages; those stages
start at the empty set, reach the initial set after one application, and each
successor stage adjoins one further relational image. -/
theorem finite_step_expansion_with_initial_stages
    {X Index : Type*} (relation : SetRel X X) (initial : Set X)
    (family : Index -> Set X) :
    relation.image (⋃ i, family i) = ⋃ i, relation.image (family i) ∧
      (reachStep relation initial).lfp =
        ⋃ n : ℕ, (reachStep relation initial)^[n] ∅ ∧
      (reachStep relation initial)^[0] ∅ = ∅ ∧
      (reachStep relation initial)^[1] ∅ = initial ∧
      ∀ n : ℕ, (reachStep relation initial)^[n + 1] ∅ =
        initial ∪ relation.image ((reachStep relation initial)^[n] ∅) := by
  have expansion := finite_step_expansion relation initial family
  refine ⟨expansion.1, expansion.2, rfl, ?_, ?_⟩
  · change initial ∪ relation.image ∅ = initial
    simp
  · intro n
    rw [← Nat.succ_eq_add_one, Function.iterate_succ_apply']
    rfl

#print axioms finite_step_expansion_with_initial_stages

end D5.S1.FixedPoints.Reachability.RelationalReachStageExpansion
