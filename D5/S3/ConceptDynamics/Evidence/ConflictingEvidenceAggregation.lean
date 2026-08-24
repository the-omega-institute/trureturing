/- GID: D5/S3/ConceptDynamics/Evidence/ConflictingEvidenceAggregation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Evidence/ConflictingEvidenceAggregation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Negative support joins true-only evidence into a both-supported state. -/

import D5.S3.ConceptDynamics.Evidence.EvidenceFourPhaseLaw

/- Library-search audit trail (2026-08-24):
   * Exact atom-id search across `D5`, `Blueprint`, digestion formalizations, and accepted
     freezes found no prior receipt or declaration.
   * Cross-tree searches found no existing two-bit support value, componentwise information
     order, or componentwise-disjunction evidence join. The imported `EvidencePhase` instead
     classifies finite evidence fibers and is not a duplicate of this source carrier.
   * Pinned-Mathlib searches for a `Bool × Bool` evidence lattice found only unrelated parser
     and integration tuples. Boolean disjunction, product projections, and Boolean order are
     applied directly; no library theorem packages the source computation.
   * External `loogle` and `leansearch` executables are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Evidence.ConflictingEvidenceAggregation

/-- Positive and negative support bits for one proposition. -/
abbrev EvidenceValue := Bool × Bool

/-- Evidence supporting only the proposition. -/
def trueOnly : EvidenceValue := (true, false)

/-- Evidence supporting only the proposition's negation. -/
def falseOnly : EvidenceValue := (false, true)

/-- Evidence with support for both the proposition and its negation. -/
def bothSupported : EvidenceValue := (true, true)

/-- Evidence aggregation retains either source's support in each coordinate. -/
def aggregateEvidence (first second : EvidenceValue) : EvidenceValue :=
  (first.1 || second.1, first.2 || second.2)

/-- The source information order is coordinatewise Boolean order. -/
def InformationLe (first second : EvidenceValue) : Prop :=
  first.1 ≤ second.1 ∧ first.2 ≤ second.2

/-- An evidence value is consistent when at least one polarity lacks support. -/
def EvidenceConsistent (value : EvidenceValue) : Prop :=
  value.1 = false ∨ value.2 = false

/-- Adding a source that supports the negation moves true-only evidence to
both-supported evidence, strictly increases information, and exposes conflict. -/
theorem negative_evidence_moves_true_only_to_both
    (additionalSource : EvidenceValue)
    (supportsNegation : additionalSource.2 = true) :
    let aggregated := aggregateEvidence trueOnly additionalSource
    aggregated = bothSupported ∧
      (InformationLe trueOnly aggregated ∧
        InformationLe additionalSource aggregated ∧
        trueOnly ≠ aggregated) ∧
      (EvidenceConsistent trueOnly ∧ ¬EvidenceConsistent aggregated) ∧
      (aggregated.1 = true ∧ aggregated.2 = true) := by
  rcases additionalSource with ⟨positiveSupport, negativeSupport⟩
  cases positiveSupport <;> cases negativeSupport <;>
    simp_all [aggregateEvidence, trueOnly, bothSupported,
      InformationLe, EvidenceConsistent]

/-- The canonical negative-only source realizes the corollary's premise. -/
example : (falseOnly : EvidenceValue).2 = true := by
  rfl

#print axioms negative_evidence_moves_true_only_to_both

end D5.S3.ConceptDynamics.Evidence.ConflictingEvidenceAggregation
