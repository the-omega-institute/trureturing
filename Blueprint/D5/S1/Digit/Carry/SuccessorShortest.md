# Alternating Successor Folds and Shortest Carry Paths

## Abstract

Alternating Successor Folds and Shortest Carry Paths.

**Theorem 1.1 (A lower bound for every directed carry path).**

Lean statement: `D5/S1/Digit/Carry/SuccessorShortest.carry_steps_mass_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/SuccessorShortest.carry_steps_mass_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite path of the four directed Fibonacci carry rules, the initial total coefficient mass is at most the final mass plus the path length. An adjacent carry or a carry on two tokens at index zero removes one token; the other two rules preserve the mass. Induction along the path gives the bound.

**Theorem 1.2 (Exact bit changes and the shortest successor path).**

Lean statement: `D5/S1/Digit/Carry/SuccessorShortest.successor_erasure_and_shortest`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/SuccessorShortest.successor_erasure_and_shortest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a canonical Zeckendorf row, take the maximal occupied alternating segment starting at zero when the lowest bit is occupied, and starting at one otherwise. Let its length be k; it is zero when both low bits are empty. The successor erases exactly those k bits and inserts exactly one previously empty bit, leaving every other bit unchanged. Its Hamming distance is k plus one, also equal to two plus the old occupied-bit count minus the new count. The minimum number of carry rewrites is k, attained by the alternating fold and bounded below for every allowed path by the decrease in coefficient mass. Adding the initial unit is an input operation and contributes no carry rewrite.

## References

- Truth anchor: `D5/S1/Digit/Carry/SuccessorShortest.carry_steps_mass_lower_bound`
- Truth anchor: `D5/S1/Digit/Carry/SuccessorShortest.successor_erasure_and_shortest`
- Dependency: [D5/S1/Digit/Carry/Successor](Successor.md)
