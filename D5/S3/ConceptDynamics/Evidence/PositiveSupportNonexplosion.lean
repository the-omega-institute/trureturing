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
     theorem. Product swapping and finite Boolean computation are used directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.ConceptDynamics.Evidence.ConflictingEvidenceAggregation

namespace D5.S3.ConceptDynamics.Evidence.PositiveSupportNonexplosion

/-- A three-formula countervaluation preserves the source negation rule, gives
positive support to a proposition and its negation, and withholds positive
support from the conclusion. Thus positive-support preservation does not
validate explosion, even though the premise evidence is inconsistent. -/
theorem positive_support_nonexplosion :
    let proposition : Fin 3 := 0
    let negatedProposition : Fin 3 := 1
    let conclusion : Fin 3 := 2
    let positivelyEntails : Prop :=
      ∀ candidateValuation : Fin 3 -> EvidenceValue,
        candidateValuation negatedProposition =
            Prod.swap (candidateValuation proposition) ->
          ((candidateValuation proposition).1 = true ∧
              (candidateValuation negatedProposition).1 = true) ->
            (candidateValuation conclusion).1 = true
    ∃ valuation : Fin 3 -> EvidenceValue,
      valuation proposition = bothSupported ∧
      valuation negatedProposition = Prod.swap (valuation proposition) ∧
      (valuation proposition).1 = true ∧
      (valuation negatedProposition).1 = true ∧
      valuation conclusion = (false, false) ∧
      (valuation conclusion).1 = false ∧
      (¬EvidenceConsistent (valuation proposition) ∧ ¬positivelyEntails) := by
  dsimp
  let valuation : Fin 3 -> EvidenceValue := fun formula =>
    if formula = 0 then bothSupported
    else if formula = 1 then Prod.swap bothSupported
    else (false, false)
  have atProposition : valuation 0 = bothSupported := by
    simp [valuation]
  have atNegatedProposition : valuation 1 = Prod.swap (valuation 0) := by
    simp [valuation]
  have atConclusion : valuation 2 = (false, false) := by
    simp [valuation]
  have propositionSupported : (valuation 0).1 = true := by
    simp [atProposition, bothSupported]
  have negatedPropositionSupported : (valuation 1).1 = true := by
    simp [atNegatedProposition, atProposition, bothSupported]
  have conclusionUnsupported : (valuation 2).1 = false := by
    simp [atConclusion]
  have evidenceInconsistent : ¬EvidenceConsistent (valuation 0) := by
    simp [atProposition, EvidenceConsistent, bothSupported]
  have doesNotEntail :
      ¬∀ candidateValuation : Fin 3 -> EvidenceValue,
        candidateValuation 1 = Prod.swap (candidateValuation 0) ->
          ((candidateValuation 0).1 = true ∧
              (candidateValuation 1).1 = true) ->
            (candidateValuation 2).1 = true := by
    intro entails
    have conclusionSupported := entails valuation atNegatedProposition
      ⟨propositionSupported, negatedPropositionSupported⟩
    simp [atConclusion] at conclusionSupported
  exact ⟨valuation, atProposition, atNegatedProposition,
    propositionSupported, negatedPropositionSupported, atConclusion,
    conclusionUnsupported, evidenceInconsistent, doesNotEntail⟩

#print axioms positive_support_nonexplosion

end D5.S3.ConceptDynamics.Evidence.PositiveSupportNonexplosion
