/- GID: D5/S3/ConceptDynamics/Identifiability/BinaryIdentificationRepairDepthEquality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Identifiability/BinaryIdentificationRepairDepthEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unconstrained binary identification depth equals exact repair width. -/

import D5.S3.ConceptDynamics.Coding.BinaryProtocolDepthLowerBound
import Batteries.Data.BitVec.Lemmas

/- Library-search audit trail (2026-08-26):
   * Exact repository hits `BinaryProtocol`, `IdentifiesGiven`, and
     `worstFiberDiversity` supply the canonical source protocol and fiber count.
   * Exact repository hit `arbitrary_binary_questions_identify_target` supplies
     the predecessor construction, but its target `Fintype` premise is unused.
   * Exact repository hit `adaptive_binary_protocol_depth_lower_bound` supplies
     the matching lower bound for every identifying adaptive protocol.
   * Exact repository hit `binary_repair_cost_is_log_of_minimal_labels` supplies
     the least feasible fixed-width repair label. No repository theorem combines
     both least elements and their equality; pinned Mathlib supplies `IsLeast`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identifiability.BinaryIdentificationRepairDepthEquality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
open D5.S3.ConceptDynamics.Coding.BinaryRepairCost
open D5.S3.ConceptDynamics.Coding.BinaryProtocolDepthLowerBound

/-- With arbitrary binary questions, the least identifying adaptive depth and
the least exact binary repair width both exist and equal the ceiling binary
logarithm of the worst target diversity in a current-concept fiber. -/
theorem unconstrained_binary_identification_depth_equals_repair_bits
    {X C Target : Type*} [Fintype X] [Fintype C]
    (current : Concept X C) (target : Concept X Target) :
    exists adaptiveDepth repairBits : Nat,
      IsLeast
          {depth | exists protocol : BinaryProtocol X depth,
            IdentifiesGiven current target protocol}
          adaptiveDepth /\
        IsLeast {width | BinaryRepairFeasible current target width} repairBits /\
        adaptiveDepth = repairBits /\
        repairBits = Nat.clog 2 (worstFiberDiversity current target) := by
  let optimum := Nat.clog 2 (worstFiberDiversity current target)
  have repairLeast :
      IsLeast {width | BinaryRepairFeasible current target width} optimum := by
    simpa only [optimum] using
      (binary_repair_cost_is_log_of_minimal_labels current target).2
  obtain ⟨label, labelDetermines⟩ := repairLeast.1
  let transcript : Concept X (BitVec optimum) := fun x => BitVec.ofFnLE (label x)
  let protocol : BinaryProtocol X optimum :=
    { transcript := transcript
      question := fun round _history x => label x round
      transcript_consistent := by
        intro x round
        simp only [transcript, BitVec.getLsb_ofFnLE] }
  have adaptiveFeasible :
      exists identifyingProtocol : BinaryProtocol X optimum,
        IdentifiesGiven current target identifyingProtocol := by
    refine ⟨protocol, ?_⟩
    intro x y sameCurrent sameTranscript
    apply labelDetermines x y sameCurrent
    funext round
    have sameBit := congrArg (fun bits => bits.getLsb round) sameTranscript
    simpa only [protocol, transcript, BitVec.getLsb_ofFnLE] using sameBit
  refine ⟨optimum, optimum, ⟨adaptiveFeasible, ?_⟩, repairLeast, rfl, rfl⟩
  rintro depth ⟨identifyingProtocol, identifies⟩
  exact adaptive_binary_protocol_depth_lower_bound current target identifyingProtocol identifies

#print axioms unconstrained_binary_identification_depth_equals_repair_bits

end D5.S3.ConceptDynamics.Identifiability.BinaryIdentificationRepairDepthEquality
