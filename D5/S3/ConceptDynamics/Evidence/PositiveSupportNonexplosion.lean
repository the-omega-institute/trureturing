/- GID: D5/S3/ConceptDynamics/Evidence/PositiveSupportNonexplosion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Evidence/PositiveSupportNonexplosion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A both-supported proposition and its negation do not entail an unsupported conclusion. -/

import D5.S3.ConceptDynamics.Evidence.ConflictingEvidenceAggregation

/- Library-search audit trail (2026-08-30):
   * Repository searches by non-explosion, positive-support consequence, and
     two-bit evidence body shape found no exact theorem.
   * The imported module owns the canonical two-bit evidence carrier, the
     both-supported value, and evidence consistency; they are reused here.
   * Pinned Mathlib searches found no packaged four-valued non-explosion
     theorem. Product swapping and classical formula equality are used directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.ConceptDynamics.Evidence.ConflictingEvidenceAggregation

namespace D5.S3.ConceptDynamics.Evidence.PositiveSupportNonexplosion

/-- For any distinct proposition, its negation, and unsupported conclusion, a
countervaluation preserves the source negation rule and gives positive support
to the first two formulas only. Thus positive-support preservation does not
validate explosion, even though the premise evidence is inconsistent. -/
theorem positive_support_nonexplosion
    {Formula : Type}
    (proposition negatedProposition conclusion : Formula)
    (proposition_ne_negatedProposition : proposition ≠ negatedProposition)
    (conclusion_ne_proposition : conclusion ≠ proposition)
    (conclusion_ne_negatedProposition : conclusion ≠ negatedProposition) :
    let positivelyEntails : Prop :=
      ∀ candidateValuation : Formula -> EvidenceValue,
        candidateValuation negatedProposition =
            Prod.swap (candidateValuation proposition) ->
          ((candidateValuation proposition).1 = true ∧
              (candidateValuation negatedProposition).1 = true) ->
            (candidateValuation conclusion).1 = true
    ∃ valuation : Formula -> EvidenceValue,
      valuation proposition = bothSupported ∧
      valuation negatedProposition = Prod.swap (valuation proposition) ∧
      (valuation proposition).1 = true ∧
      (valuation negatedProposition).1 = true ∧
      valuation conclusion = (false, false) ∧
      (valuation conclusion).1 = false ∧
      (¬EvidenceConsistent (valuation proposition) ∧ ¬positivelyEntails) := by
  classical
  dsimp
  let valuation : Formula -> EvidenceValue := fun formula =>
    if formula = proposition then bothSupported
    else if formula = negatedProposition then Prod.swap bothSupported
    else (false, false)
  have atProposition : valuation proposition = bothSupported := by
    simp [valuation]
  have atNegatedProposition :
      valuation negatedProposition = Prod.swap (valuation proposition) := by
    have negatedProposition_ne_proposition :
        negatedProposition ≠ proposition :=
      Ne.symm proposition_ne_negatedProposition
    simp [valuation, negatedProposition_ne_proposition]
  have atConclusion : valuation conclusion = (false, false) := by
    simp [valuation, conclusion_ne_proposition,
      conclusion_ne_negatedProposition]
  have propositionSupported : (valuation proposition).1 = true := by
    simp [atProposition, bothSupported]
  have negatedPropositionSupported :
      (valuation negatedProposition).1 = true := by
    simp [atNegatedProposition, atProposition, bothSupported]
  have conclusionUnsupported : (valuation conclusion).1 = false := by
    simp [atConclusion]
  have evidenceInconsistent :
      ¬EvidenceConsistent (valuation proposition) := by
    simp [atProposition, EvidenceConsistent, bothSupported]
  have doesNotEntail :
      ¬∀ candidateValuation : Formula -> EvidenceValue,
        candidateValuation negatedProposition =
            Prod.swap (candidateValuation proposition) ->
          ((candidateValuation proposition).1 = true ∧
              (candidateValuation negatedProposition).1 = true) ->
            (candidateValuation conclusion).1 = true := by
    intro entails
    have conclusionSupported := entails valuation atNegatedProposition
      ⟨propositionSupported, negatedPropositionSupported⟩
    simp [atConclusion] at conclusionSupported
  exact ⟨valuation, atProposition, atNegatedProposition,
    propositionSupported, negatedPropositionSupported, atConclusion,
    conclusionUnsupported, evidenceInconsistent, doesNotEntail⟩

#print axioms positive_support_nonexplosion

end D5.S3.ConceptDynamics.Evidence.PositiveSupportNonexplosion
