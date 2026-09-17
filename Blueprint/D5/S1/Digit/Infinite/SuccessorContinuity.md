# Continuity of the First Adjacent Zero Successor

## Abstract

Continuity of the First Adjacent Zero Successor.

**Theorem 1.1 (Continuity on infinite legal digits).**

Lean statement: `D5/S1/Digit/Infinite/SuccessorContinuity.infinite_successor_continuous`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SuccessorContinuity.infinite_successor_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An infinite legal Boolean sequence has no adjacent ones. Its successor erases the digits below the first adjacent zero pair, puts a one at the first position of that pair, and retains the higher digits. A sequence with no adjacent zero pair is sent to the zero sequence. Agreement on the first N plus one input digits forces agreement on the first N output digits: an earlier zero pair has the same first position in both inputs, while the absence of such a pair makes both output prefixes zero. This proves continuity into the ambient product of discrete Boolean spaces, including at both alternating sequences.

## References

- Truth anchor: `D5/S1/Digit/Infinite/SuccessorContinuity.infinite_successor_continuous`
