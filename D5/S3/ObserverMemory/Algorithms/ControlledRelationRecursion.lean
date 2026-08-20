/- GID: D5/S3/ObserverMemory/Algorithms/ControlledRelationRecursion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/ControlledRelationRecursion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bounded controlled behavior relations satisfy the current-readout recursion. -/

import D5.S3.ObserverMemory.Algorithms.ControlledSignatureStabilization

/- Library-search audit trail (2026-08-20):
   * Repository search found the exact source-semantics constructions `runWord`
     and `boundedWordEquivalent` in the frozen controlled behavior modules.
     They are imported and reused below. The public correctness theorem there
     relates bounded words to signatures but does not state this relation
     recursion.
   * Pinned-Mathlib search found `Set.ext`, `Set.mem_iInter`, and
     `Set.mem_preimage`; they are applied below to expose set equality,
     universal intersection membership, and successor-pair preimages.
   * No repository or pinned-Mathlib theorem was found that packages both the
     depth-zero kernel equation and the all-input successor equation. -/

namespace D5.S3.ObserverMemory.Algorithms.ControlledRelationRecursion

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.ControlledSignatureStabilization

universe u

/-- Pairs with equal current readout, constructed from the readout map. -/
def readoutKernel {Y : Type*} {O : Type u} (readout : Y -> O) : Set (Y × Y) :=
  {pair | readout pair.1 = readout pair.2}

/-- The depth relation constructed from equality of readouts after every
input word whose length is at most the given depth. -/
def controlledDepthRelation {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) (depth : Nat) : Set (Y × Y) :=
  {pair | boundedWordEquivalent update readout depth pair.1 pair.2}

/-- The bounded controlled behavior relation starts at the readout kernel.
At the next depth it is the current kernel intersected with the preimage of
the preceding relation under every controlled successor map. -/
theorem controlled_behavior_relation_recursion {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) (depth : Nat) :
    controlledDepthRelation update readout 0 = readoutKernel readout ∧
      controlledDepthRelation update readout (depth + 1) =
        readoutKernel readout ∩
          ⋂ input : U,
            (Prod.map (update input) (update input)) ⁻¹'
              controlledDepthRelation update readout depth := by
  constructor
  · ext pair
    change boundedWordEquivalent update readout 0 pair.1 pair.2 ↔
      readout pair.1 = readout pair.2
    constructor
    · intro h
      simpa [runWord] using h [] (Nat.zero_le 0)
    · intro h word hlength
      have hword : word = [] :=
        List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlength)
      subst word
      simpa [runWord] using h
  · ext pair
    change boundedWordEquivalent update readout (depth + 1) pair.1 pair.2 ↔
      readout pair.1 = readout pair.2 ∧
        pair ∈ ⋂ input : U,
          (Prod.map (update input) (update input)) ⁻¹'
            controlledDepthRelation update readout depth
    constructor
    · intro h
      refine ⟨?_, Set.mem_iInter.mpr ?_⟩
      · simpa [runWord] using h [] (Nat.zero_le (depth + 1))
      · intro input
        change boundedWordEquivalent update readout depth
          (update input pair.1) (update input pair.2)
        intro word hlength
        have hbounded : (input :: word).length ≤ depth + 1 := by
          simpa using Nat.succ_le_succ hlength
        simpa [runWord] using h (input :: word) hbounded
    · rintro ⟨hcurrent, hsuccessors⟩ word hlength
      cases word with
      | nil =>
          simpa [runWord] using hcurrent
      | cons input tail =>
          have htail : tail.length ≤ depth := by
            simpa using Nat.le_of_succ_le_succ hlength
          have hsuccessor := Set.mem_iInter.mp hsuccessors input
          change boundedWordEquivalent update readout depth
            (update input pair.1) (update input pair.2) at hsuccessor
          simpa [runWord] using hsuccessor tail htail

/-- The carrier and maps in the theorem have a concrete inhabited model. -/
example : Unit -> Unit -> Unit := fun _ => id

example : Unit -> Unit := id

#print axioms controlled_behavior_relation_recursion

end D5.S3.ObserverMemory.Algorithms.ControlledRelationRecursion
