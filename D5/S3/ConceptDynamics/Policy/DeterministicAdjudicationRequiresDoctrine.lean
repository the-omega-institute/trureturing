/- GID: D5/S3/ConceptDynamics/Policy/DeterministicAdjudicationRequiresDoctrine
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Policy/DeterministicAdjudicationRequiresDoctrine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct licensed outcomes require doctrine beyond the public-law value. -/

import D5.S3.ConceptDynamics.Policy.DiscretionaryOutcomeNonuniqueness
import Mathlib.Logic.Relator

/- Library-search audit trail (2026-09-05):
   * Exact D5 core hit
     `Policy.DiscretionaryOutcomeNonuniqueness.discretionary_outcome_nonuniqueness`
     proves that two licensed outcomes in one public-law fiber rule out unique
     existence; it is applied directly below.
   * D5 body-shape searches for `DoctrineInput`, `priority.*equity`,
     `RightUnique.*doctrine`, and `doctrine.*RightUnique` found no carrier or
     theorem encoding the six source alternatives.
   * `CompleteInputDeterminism` is adjacent but uses a different eight-field
     complete-input carrier and does not state this six-way doctrine interface.
   * Pinned Mathlib defines `Relator.RightUnique` in `Mathlib.Logic.Relator`;
     the exact relational determinism primitive is used directly. Searches for
     a source-specific permitted-outcome theorem found no additional exact hit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Policy.DeterministicAdjudicationRequiresDoctrine

open D5.S3.ConceptDynamics.Policy.DiscretionaryOutcomeNonuniqueness

/-- Information beyond the public-law value may enter an adjudication through
priority, equity, a historical anchor, value weights, a randomized selector,
or a finer fact concept. Each constructor retains the source-level payload
rather than identifying doctrine with a desired outcome. -/
inductive AdjudicationDoctrine
    (Case Outcome Weight Seed FineFact : Type*) where
  | priority (precedes : Outcome -> Outcome -> Prop)
  | equity (equitable : Case -> Outcome -> Prop)
  | historicalAnchor (anchor : Case)
  | valueWeight (weight : Outcome -> Weight)
  | randomChoice (seed : Seed) (select : Seed -> Outcome)
  | finerFactConcept (readout : Case -> FineFact)

/-- If two distinct outcomes are licensed for admissible cases with the same
public-law value, that value neither uniquely determines an outcome nor lets a
right-unique public-only relation realize both. If a right-unique adjudicator
does realize both after adding one of the listed doctrine inputs, those inputs
must differ. -/
theorem deterministic_adjudication_requires_additional_doctrine
    {Case PublicFact Outcome Weight Seed FineFact : Type*}
    (publicLaw : Case -> PublicFact)
    (admissible : Case -> Prop)
    (permitted : Case -> Outcome -> Prop)
    (b : PublicFact)
    (leftOutcome rightOutcome : Outcome)
    (distinct : leftOutcome ≠ rightOutcome)
    (leftPermitted :
      ∃ x, admissible x ∧ publicLaw x = b ∧ permitted x leftOutcome)
    (rightPermitted :
      ∃ x, admissible x ∧ publicLaw x = b ∧ permitted x rightOutcome) :
    (¬ ∃! outcome,
      ∃ x, admissible x ∧ publicLaw x = b ∧ permitted x outcome) ∧
    (¬ ∃ publicAdjudicator : PublicFact -> Outcome -> Prop,
      Relator.RightUnique publicAdjudicator ∧
        publicAdjudicator b leftOutcome ∧
        publicAdjudicator b rightOutcome) ∧
    ∀ (adjudicator :
        (PublicFact ×
          AdjudicationDoctrine Case Outcome Weight Seed FineFact) ->
            Outcome -> Prop),
      Relator.RightUnique adjudicator ->
      ∀
      (leftDoctrine rightDoctrine :
        AdjudicationDoctrine Case Outcome Weight Seed FineFact),
      adjudicator (b, leftDoctrine) leftOutcome ->
      adjudicator (b, rightDoctrine) rightOutcome ->
      leftDoctrine ≠ rightDoctrine := by
  constructor
  · exact
      discretionary_outcome_nonuniqueness publicLaw admissible permitted b
        ⟨leftOutcome, rightOutcome, distinct, leftPermitted, rightPermitted⟩
  constructor
  · rintro ⟨publicAdjudicator, deterministic, leftDecision, rightDecision⟩
    exact distinct (deterministic leftDecision rightDecision)
  · intro adjudicator deterministic leftDoctrine rightDoctrine
      leftDecision rightDecision sameDoctrine
    apply distinct
    subst rightDoctrine
    exact deterministic leftDecision rightDecision

#print axioms AdjudicationDoctrine
#print axioms deterministic_adjudication_requires_additional_doctrine

end D5.S3.ConceptDynamics.Policy.DeterministicAdjudicationRequiresDoctrine
