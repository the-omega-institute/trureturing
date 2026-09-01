/- GID: D5/S3/ConceptDynamics/Refinement/RelativeMaturityIsFixedPoint
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/RelativeMaturityIsFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relative maturity is exactly answerability of every question in the family. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-23):
   * `rg -n -F 'mature_iff_all_questions_answerable' D5 Golden/Frozen/accepted`,
     and searches for `MatureFor` and `RelativeMaturity` returned no hits.
   * `rg -n -F 'concept_join_universal' D5` found the canonical binary completion
     universal property in `ConceptDynamics.ConceptJoinUniversal`; it supplies both
     join projections and the least-common-refinement factorization used below.
   * Searches for `Refines`, `conceptJoin`, and `AnswerabilityCriterion` found no
     existing family-level fixed-point characterization or relative-maturity witness.
     The proof reuses `concept_join_universal` and elementary function composition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Refinement.RelativeMaturityIsFixedPoint

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A concept is mature for a question family when every joint completion refines it. -/
def MatureFor {ι X C V : Type _} (q_C : Concept X C)
    (questions : ι -> Concept X V) : Prop :=
  ∀ n, Refines (conceptJoin q_C (questions n)) q_C

/-- Relative maturity is equivalent to every question already factoring through the concept. -/
theorem mature_iff_all_questions_answerable
    {ι X C V : Type _} (q_C : Concept X C) (questions : ι -> Concept X V) :
    MatureFor q_C questions ↔ ∀ n, Refines (questions n) q_C := by
  constructor
  · intro mature n
    rcases mature n with ⟨collapse, hcollapse⟩
    rcases (concept_join_universal q_C (questions n)
      (conceptJoin q_C (questions n))).2.1 with ⟨project, hproject⟩
    refine ⟨project ∘ collapse, ?_⟩
    rw [hproject, hcollapse]
    unfold Function.comp
    rfl
  · intro answerable n
    exact (concept_join_universal q_C (questions n) q_C).2.2
      ⟨id, rfl⟩ (answerable n)

/-- Maturity can hold for one question family and fail for another on the same concept. -/
theorem relative_maturity_is_not_absolute :
    ∃ (q_C : Concept (Bool × Bool) Bool)
      (questions questions' : Unit -> Concept (Bool × Bool) Bool),
      MatureFor q_C questions ∧ ¬ MatureFor q_C questions' := by
  refine ⟨Prod.fst, (fun _ : Unit => Prod.fst), (fun _ : Unit => Prod.snd), ?_, ?_⟩
  · exact (mature_iff_all_questions_answerable Prod.fst
      (fun _ : Unit => Prod.fst)).2 (fun _ => ⟨id, rfl⟩)
  · intro mature
    have answerable :
        Refines (Prod.snd : Bool × Bool -> Bool) (Prod.fst : Bool × Bool -> Bool) :=
      (mature_iff_all_questions_answerable Prod.fst
        (fun _ : Unit => Prod.snd)).1 mature ()
    rcases answerable with ⟨factor, hfactor⟩
    have collapsed :
        (Prod.snd : Bool × Bool -> Bool) (false, false) =
          (Prod.snd : Bool × Bool -> Bool) (false, true) := by
      rw [hfactor]
      rfl
    exact Bool.false_ne_true collapsed

example : MatureFor (Prod.fst : Bool × Bool -> Bool) (fun _ : Unit => Prod.fst) := by
  exact (mature_iff_all_questions_answerable Prod.fst
    (fun _ : Unit => Prod.fst)).2 (fun _ => ⟨id, rfl⟩)

#print axioms mature_iff_all_questions_answerable

end D5.S3.ConceptDynamics.Refinement.RelativeMaturityIsFixedPoint
