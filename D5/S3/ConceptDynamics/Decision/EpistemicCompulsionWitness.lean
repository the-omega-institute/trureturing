/- GID: D5/S3/ConceptDynamics/Decision/EpistemicCompulsionWitness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Decision/EpistemicCompulsionWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A coarse observation can erase every jointly safe action despite pointwise legality. -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-27):
   * Repository searches for fiber-safe actions, ignorance, and epistemic compulsion found no
     exact theorem or canonical safe-action primitive.
   * The source defines fiber safety directly by universal legality over an observation fiber;
     the public statement exposes that predicate without introducing a duplicate named definition.
   * Pinned Mathlib supplies the finite Bool and Unit carriers but no packaged countermodel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Decision.EpistemicCompulsionWitness

/-- Two indistinguishable states can each admit an action while admitting no one action that is
legal throughout their common observation fiber. -/
theorem epistemic_compulsion_witness :
    exists (observation : Bool -> Unit) (legal : Bool -> Bool -> Prop) (z : Unit),
      (forall state, exists action, legal state action) /\
        (forall state action, legal state action <-> action = state) /\
        (forall state, observation state = z) /\
        ¬ exists action, forall state, observation state = z -> legal state action := by
  refine ⟨fun _ => (), fun state action => action = state, (), ?_, ?_, ?_, ?_⟩
  · intro state
    exact ⟨state, rfl⟩
  · intro state action
    rfl
  · intro state
    rfl
  · rintro ⟨action, safe⟩
    have atFalse : action = false := safe false rfl
    have atTrue : action = true := safe true rfl
    rw [atFalse] at atTrue
    exact Bool.noConfusion atTrue

#print axioms epistemic_compulsion_witness

end D5.S3.ConceptDynamics.Decision.EpistemicCompulsionWitness
