/- GID: D5/S3/ConceptDynamics/Policy/DiscretionaryOutcomeNonuniqueness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Policy/DiscretionaryOutcomeNonuniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two licensed outcomes in one public-law fiber rule out unique determination. -/

import Mathlib.Logic.ExistsUnique

/- Library-search audit trail (2026-08-27):
   * Repository name and body-shape searches found no theorem negating unique
     legal outcomes from two witnesses in one public-law fiber.
   * `DeterministicPolicySectionCount` adds finiteness, global nonemptiness, and
     selected-family hypotheses, so it is not an exact source-level hit.
   * Pinned Mathlib supplies the generic `ExistsUnique` predicate but no exact
     theorem for the source-constructed admissibility and permission relation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Policy.DiscretionaryOutcomeNonuniqueness

/-- Two distinct outcomes licensed for admissible cases with the same public
law value prevent that public interface from uniquely determining an outcome. -/
theorem discretionary_outcome_nonuniqueness
    {Case PublicFact Outcome : Type*}
    (publicLaw : Case -> PublicFact)
    (admissible : Case -> Prop)
    (permitted : Case -> Outcome -> Prop)
    (b : PublicFact)
    (multipleOutcomes :
      ∃ leftOutcome rightOutcome,
        leftOutcome ≠ rightOutcome ∧
          (∃ x, admissible x ∧ publicLaw x = b ∧ permitted x leftOutcome) ∧
          ∃ x, admissible x ∧ publicLaw x = b ∧ permitted x rightOutcome) :
    ¬ ∃! outcome,
      ∃ x, admissible x ∧ publicLaw x = b ∧ permitted x outcome := by
  rintro ⟨chosen, chosenPermitted, unique⟩
  rcases multipleOutcomes with
    ⟨leftOutcome, rightOutcome, distinct, leftPermitted, rightPermitted⟩
  have left_eq : leftOutcome = chosen := unique leftOutcome leftPermitted
  have right_eq : rightOutcome = chosen := unique rightOutcome rightPermitted
  exact distinct (left_eq.trans right_eq.symm)

#print axioms discretionary_outcome_nonuniqueness

end D5.S3.ConceptDynamics.Policy.DiscretionaryOutcomeNonuniqueness
