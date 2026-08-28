/- GID: D5/S3/ConceptDynamics/InterventionLaws/OracleLawErrorDetection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionLaws/OracleLawErrorDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact intervention-law codewords decode uniquely below half their minimum distance. -/

import D5.S3.Arith.Coding.UniqueDecodingRadius
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-08-26):
   * The current-tree search for unique Hamming decoding found
     `UniqueDecodingRadius.unique_decoding_radius`; it supplies the generic
     code-set argument and is applied directly below.
   * The body-shape searches for a law-family product found the canonical
     `JointFaithfulnessLeibnizCriterion.jointReadout`, which constructs the
     source codeword here. Searches for `sInf` together with `hammingDist`
     found only the residue-specific minimum in `ExactResidueCodeMinimumDistance`.
   * Pinned Mathlib's Hamming library provides the distance primitive, but the
     exact theorem search found no intervention-law minimum-distance decoder.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionLaws.OracleLawErrorDetection

open D5.S3.Arith.Coding.ResidueCodeErrorDetection
open D5.S3.Arith.Coding.UniqueDecodingRadius
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-- The least coordinate Hamming distance between codewords of distinct models
in a finite intervention-law suite. -/
noncomputable def interventionMinimumDistance {Model Law : Type*} [DecidableEq Law] {n : ℕ}
    (law : Fin n → Model → Law) : ℕ :=
  sInf {distance | ∃ M N, M ≠ N ∧
    hammingDist (jointReadout law M) (jointReadout law N) = distance}

/-- Corrupting at most `e` exact intervention-law coordinates leaves the true
model codeword as the unique codeword within Hamming radius `e` whenever twice
that radius is below the suite's minimum distance. -/
theorem oracle_intervention_law_error_detection
    {Model Law : Type*} [DecidableEq Law] {n e : ℕ}
    (law : Fin n → Model → Law) (trueModel : Model) (received : Fin n → Law)
    (forgedCoordinates :
      hammingDist received (jointReadout law trueModel) ≤ e)
    (distanceCondition : 2 * e < interventionMinimumDistance law) :
    ∃! candidate : Fin n → Law,
      candidate ∈ Set.range (jointReadout law) ∧
        hammingDist received candidate ≤ e := by
  have hMinimum :
      MinDistanceAtLeast (Set.range (jointReadout law))
        (interventionMinimumDistance law) := by
    intro firstCode hFirst secondCode hSecond hDifferent
    rcases hFirst with ⟨firstModel, rfl⟩
    rcases hSecond with ⟨secondModel, rfl⟩
    apply Nat.sInf_le
    refine ⟨firstModel, secondModel, ?_, rfl⟩
    intro hModels
    subst secondModel
    exact hDifferent rfl
  exact (unique_decoding_radius hMinimum).1
    (jointReadout law trueModel) received e (Set.mem_range_self trueModel)
    forgedCoordinates distanceCondition

#print axioms oracle_intervention_law_error_detection

end D5.S3.ConceptDynamics.InterventionLaws.OracleLawErrorDetection
