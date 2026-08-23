/- GID: D5/S3/ConceptDynamics/Answering/InformationRefinementShrinksAnswers
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Answering/InformationRefinementShrinksAnswers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refining possible worlds shrinks their attainable answer image. -/

import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'answer_set_antitone_in_information' D5 Golden/Frozen/accepted`
     found no existing declaration or accepted duplicate.
   * Searches for information refinement, answer antitonicity, and set images under
     `D5/S3/ConceptDynamics` found no theorem about images of possible-world sets.
     `RefinementMonotoneAnswerDomain` instead concerns safe answerers under concept
     factorization, so its definitions and covariance result do not cover this claim.
   * Pinned Mathlib provides `Set.image_mono` for the main image inclusion. The strict
     Boolean witness and the contrapositive use elementary set membership and logic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Answering.InformationRefinementShrinksAnswers

/-- Answers still possible when `S` is the set of worlds not ruled out by information. -/
def Ans {World Answer : Type*} (T : World -> Answer) (S : Set World) : Set Answer :=
  T '' S

/-- Refining information by removing possible worlds cannot introduce possible answers.

This is antitone in the information order, unlike permission expansion, which enlarges
reachable states. It concerns answer images rather than experiment expansion's shrinking
of indistinguishable state pairs. -/
theorem answer_set_antitone_in_information
    {World Answer : Type*} (T : World -> Answer) {S S' : Set World}
    (hRefinement : S' ⊆ S) :
    Ans T S' ⊆ Ans T S := by
  exact Set.image_mono hRefinement

/-- On Boolean worlds, learning that the world is `true` strictly removes the answer
`false` from the answers possible under complete ignorance. -/
theorem strict_refinement_witness :
    ({true} : Set Bool) ⊂ Set.univ ∧
      Ans (id : Bool -> Bool) ({true} : Set Bool) ⊂
        Ans (id : Bool -> Bool) Set.univ := by
  simp [Ans]

/-- If possible answers have increased, the new state was not an information refinement. -/
theorem answer_growth_precludes_refinement
    {World Answer : Type*} (T : World -> Answer) {S S' : Set World}
    (hGrowth : ¬(Ans T S' ⊆ Ans T S)) :
    ¬(S' ⊆ S) := by
  intro hRefinement
  exact hGrowth (answer_set_antitone_in_information T hRefinement)

example :
    Ans (id : Bool -> Bool) ({true} : Set Bool) ⊂
      Ans (id : Bool -> Bool) Set.univ :=
  strict_refinement_witness.2

#print axioms answer_set_antitone_in_information

end D5.S3.ConceptDynamics.Answering.InformationRefinementShrinksAnswers
