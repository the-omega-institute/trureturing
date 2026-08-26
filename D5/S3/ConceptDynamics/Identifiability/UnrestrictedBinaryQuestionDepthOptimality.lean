/- GID: D5/S3/ConceptDynamics/Identifiability/UnrestrictedBinaryQuestionDepthOptimality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Identifiability/UnrestrictedBinaryQuestionDepthOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unrestricted binary questions attain the exact finite repair depth. -/

import D5.S3.ConceptDynamics.Coding.BinaryProtocolDepthLowerBound
import Batteries.Data.BitVec.Lemmas

/- Library-search audit trail (2026-08-26):
   * `arbitrary_binary_questions_identify_target` is the adjacent construction,
     but its signature carries an avoidable finite-target instance. The public
     theorem instead constructs the canonical protocol from the stronger
     least-repair-width result and keeps only the source-relevant instances.
   * Exact D5 clause hit `adaptive_binary_protocol_depth_lower_bound` supplies
     the lower bound for every identifying canonical binary protocol.
   * Exact D5 clause hit `binary_repair_cost_is_log_of_minimal_labels` supplies
     the least fixed-width binary repair cost on the same concept fibers.
   * Searches for an `IsLeast` theorem combining `BinaryProtocol`,
     `IdentifiesGiven`, and `BinaryRepairFeasible` found no exact whole-theorem
     owner in D5 or pinned Mathlib. No new semantic primitive is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identifiability.UnrestrictedBinaryQuestionDepthOptimality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
open D5.S3.ConceptDynamics.Coding.BinaryRepairCost
open D5.S3.ConceptDynamics.Coding.BinaryProtocolDepthLowerBound

/-- When arbitrary binary questions are available, the ceiling binary
logarithm of worst fiber diversity is simultaneously the least identifying
adaptive-protocol depth and the least exact binary-repair width. -/
theorem unrestricted_binary_question_depth_optimality
    {X C Target : Type*} [Fintype X] [Fintype C]
    (current : Concept X C) (target : Concept X Target) :
    IsLeast
        {depth : Nat |
          exists protocol : BinaryProtocol X depth,
            IdentifiesGiven current target protocol}
        (Nat.clog 2 (worstFiberDiversity current target)) /\
      IsLeast
        {width : Nat | BinaryRepairFeasible current target width}
        (Nat.clog 2 (worstFiberDiversity current target)) := by
  have repairLeast :=
    (binary_repair_cost_is_log_of_minimal_labels current target).2
  constructor
  · constructor
    · rcases repairLeast.1 with ⟨label, determines⟩
      let transcript : Concept X
          (BitVec (Nat.clog 2 (worstFiberDiversity current target))) :=
        fun x => BitVec.ofFnLE (label x)
      let protocol : BinaryProtocol X
          (Nat.clog 2 (worstFiberDiversity current target)) :=
        { transcript := transcript
          question := fun round _history x => label x round
          transcript_consistent := by
            intro x round
            simp [transcript] }
      refine ⟨protocol, ?_⟩
      intro x y sameCurrent sameTranscript
      apply determines x y sameCurrent
      funext round
      have sameBit := congrArg
        (fun bits : BitVec (Nat.clog 2 (worstFiberDiversity current target)) =>
          bits.getLsb round)
        sameTranscript
      simpa [protocol, transcript] using sameBit
    · rintro depth ⟨protocol, identifies⟩
      exact adaptive_binary_protocol_depth_lower_bound
        current target protocol identifies
  · exact repairLeast

#print axioms unrestricted_binary_question_depth_optimality

end D5.S3.ConceptDynamics.Identifiability.UnrestrictedBinaryQuestionDepthOptimality
