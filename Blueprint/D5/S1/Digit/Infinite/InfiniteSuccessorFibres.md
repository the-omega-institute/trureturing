# Fibres of the Infinite Digit Successor

## Abstract

Fibres of the Infinite Digit Successor.

**Theorem 1.1 (Surjectivity and all predecessors).**

Lean statement: `D5/S1/Digit/Infinite/InfiniteSuccessorFibres.next_fibres`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/InfiniteSuccessorFibres.next_fibres` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first adjacent zero successor preserves the condition that no two adjacent digits are both one, and every legal infinite Boolean sequence has a predecessor. The zero sequence has exactly two predecessors: u has ones at the even positions and v has ones at the odd positions, with positions indexed from zero. Every nonzero sequence has exactly one predecessor. Its first one determines the position of the predecessor's first adjacent zero pair, its lower digits form the unique alternating prefix, ending in one when nonempty, and its higher digits are retained.

## References

- Truth anchor: `D5/S1/Digit/Infinite/InfiniteSuccessorFibres.next_fibres`
- Dependency: [D5/S1/Digit/Infinite/SuccessorContinuity](SuccessorContinuity.md)
