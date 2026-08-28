/- GID: D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pairwise compatible local laws need not admit a joint global state. -/

import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-28):
   * Repository searches for local-law families, marginal compatibility, joint
     global states, and three-cycle constraints found adjacent gluing modules
     but no theorem exposing a compatible family with no global realization.
   * Body-shape searches for equality and inequality relations on pairwise Bool
     coordinates found no canonical D5 primitive to import. The relations stay
     theorem-local rather than becoming a competing named family primitive.
   * Pinned Mathlib supplies `Set.image` and Bool inequality facts, but no exact
     local-to-global obstruction theorem on this source carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction

/-- Three pairwise laws can agree on every one-coordinate overlap while having
no joint global realization. The same two local relations occur in both the
compatibility clauses and the failed global-state clause. -/
theorem compatible_local_laws_can_lack_global_state :
    let sameLaw : Set (Bool × Bool) := {pair | pair.1 = pair.2}
    let differentLaw : Set (Bool × Bool) := {pair | pair.1 ≠ pair.2}
    (Prod.snd '' sameLaw = Prod.fst '' sameLaw ∧
      Prod.fst '' sameLaw = Prod.fst '' differentLaw ∧
      Prod.snd '' sameLaw = Prod.snd '' differentLaw) ∧
    ¬ ∃ state : Bool × Bool × Bool,
      (state.1, state.2.1) ∈ sameLaw ∧
      (state.2.1, state.2.2) ∈ sameLaw ∧
      (state.1, state.2.2) ∈ differentLaw := by
  dsimp
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · ext value
      constructor
      · rintro ⟨pair, _, rfl⟩
        exact ⟨(pair.2, pair.2), rfl, rfl⟩
      · rintro ⟨pair, _, rfl⟩
        exact ⟨(pair.1, pair.1), rfl, rfl⟩
    · ext value
      constructor
      · rintro ⟨pair, _, rfl⟩
        exact ⟨(pair.1, !pair.1), (Bool.not_ne_self pair.1).symm, rfl⟩
      · rintro ⟨pair, _, rfl⟩
        exact ⟨(pair.1, pair.1), rfl, rfl⟩
    · ext value
      constructor
      · rintro ⟨pair, _, rfl⟩
        exact ⟨(!pair.2, pair.2), Bool.not_ne_self pair.2, rfl⟩
      · rintro ⟨pair, _, rfl⟩
        exact ⟨(pair.2, pair.2), rfl, rfl⟩
  · rintro ⟨state, sameFirst, sameSecond, differentOuter⟩
    exact differentOuter (sameFirst.trans sameSecond)

#print axioms compatible_local_laws_can_lack_global_state

end D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
