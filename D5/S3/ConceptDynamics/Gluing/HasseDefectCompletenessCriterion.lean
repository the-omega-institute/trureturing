/- GID: D5/S3/ConceptDynamics/Gluing/HasseDefectCompletenessCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/HasseDefectCompletenessCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hasse completeness is equivalent to empty positive and negative defect sets. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-26):
   * Searches for Hasse completeness, positive and negative local-global
     defects, and two empty defect sets found no exact D5 theorem.
   * `NormTwoIdealLocalGlobalGap.positiveHasseDefect` is an arithmetic-specific
     positive-defect subtype in an I-plane module; it has no negative-defect or
     completeness criterion and cannot be imported into this G-plane result.
   * Body-shape searches for both set comprehensions and their joint emptiness
     found no general D5 primitive. No new definition is introduced here: the
     source's two defect predicates occur directly in the public statement.
   * Exact pinned-Mathlib hit `Set.eq_empty_iff_forall_notMem` converts each
     defect-set equation to pointwise exclusion and is applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.HasseDefectCompletenessCriterion

/-- A global predicate agrees everywhere with all local predicates exactly
when neither a locally accepted global counterexample nor a globally accepted
local counterexample exists. -/
theorem hasse_complete_iff_positive_negative_defects_empty
    {X Index : Type*} (global : X -> Prop)
    (localPredicate : Index -> X -> Prop) :
    (forall object, global object <->
        forall index, localPredicate index object) <->
      {object : X |
          (forall index, localPredicate index object) /\ ¬ global object} = ∅ /\
      {object : X |
          global object /\ ¬ forall index, localPredicate index object} = ∅ := by
  constructor
  · intro complete
    constructor
    · rw [Set.eq_empty_iff_forall_notMem]
      intro object defect
      exact defect.2 ((complete object).2 defect.1)
    · rw [Set.eq_empty_iff_forall_notMem]
      intro object defect
      exact defect.2 ((complete object).1 defect.1)
  · rintro ⟨positiveEmpty, negativeEmpty⟩ object
    rw [Set.eq_empty_iff_forall_notMem] at positiveEmpty negativeEmpty
    constructor
    · intro globallyValid
      by_contra locallyInvalid
      exact negativeEmpty object ⟨globallyValid, locallyInvalid⟩
    · intro locallyValid
      by_contra globallyInvalid
      exact positiveEmpty object ⟨locallyValid, globallyInvalid⟩

#print axioms hasse_complete_iff_positive_negative_defects_empty

end D5.S3.ConceptDynamics.Gluing.HasseDefectCompletenessCriterion
