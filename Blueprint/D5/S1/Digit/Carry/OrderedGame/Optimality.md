# Raw Greedy Optimality for the Ordered Zeckendorf Game

## Abstract

Complete raw weighted terminal domination and the ordered terminality bridge.

All indices here are raw, zero-based indices. Raw reward includes the carry and all sorting switches paid by that carry. The concrete G is the existing greedy recursion, not a supremum or a maximum over competing paths.

**Theorem 1.1 (Finite singleton merge cascade).**

Lean statement: `D5/S1/Digit/Carry/OrderedGame/Optimality.singleton_merge_cascade`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Optimality.singleton_merge_cascade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive-index singleton merge followed by the finite high cascade yields a binary upper tail, preserves lower coordinates, and replays with the same reward under arbitrary lower-boundary changes. The lower input must remain positive; higher coordinates agree.

**Theorem 1.2 (Extract a lower split across a finite high cascade).**

Lean statement: `D5/S1/Digit/Carry/OrderedGame/Optimality.lower_split_merge_exchange`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Optimality.lower_split_merge_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the actual high cascade, the lower nonzero split is again preferred with its original reward. Taking it first permits legal replay to the same endpoint, including j=a-1.

**Theorem 1.3 (Exchange separated merge blocks).**

Lean statement: `D5/S1/Digit/Carry/OrderedGame/Optimality.binary_separated_merge_exchange`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Optimality.binary_separated_merge_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a binary state, a competing merge at b at least a+3 completes its actual high cascade before the least merge a. Replaying the high block after a is legal with equal reward and a common endpoint, including b=a+3 where the coordinate below the block changes.

**Theorem 1.4 (Every complete legal raw path is bounded by G).**

Lean statement: `D5/S1/Digit/Carry/OrderedGame/Optimality.raw_terminal_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Optimality.raw_terminal_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every RawPath c e w with CanonicalRaw e, w is at most G c. There is no restriction on the raw start, spectator multiplicities or interleaving of merges and splits. Strict carry-measure induction first establishes every one-step comparison at c. Ones use terminal promotion; nonzero split competitors use the actual split-prefix cut before merges are considered. Shared-input repairs and the singleton exchanges settle the remaining merges. Binary states use an inner strong induction on the competing merge index. Every use of terminal optimality is at a strict successor, and every equality for G follows from an actual greedy path. Together with the existing complete_greedy_reward this proves weighted raw optimality for every complete raw greedy path.

**Theorem 1.5 (Ordered terminality implies canonical raw digits).**

Lean statement: `D5/S1/Digit/Carry/OrderedGame/Optimality.terminal_raw_canonical`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Optimality.terminal_raw_canonical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absence of all five actual adjacent moves forces a gap of at least two between neighboring list entries. Transitivity makes the whole list spaced, hence its raw multiplicities are binary and nonconsecutive. The proof includes the exceptional zero and one splits.

The full source Conjecture 1.7 remains unproved. The remaining interfaces are ordered LGS priority correspondence and erasure to raw greedy paths, existence of a complete ordered LGS path for every positive n, and the final comparison using exact ordered potential attainment. No helper counts as a completed external problem. Attribution remains with Bortnovskyi et al., Cusenza et al., and the existing suppliers in PRs 7495, 7575, 7643 and 7651; no worldwide priority claim is made.

## References

- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Optimality.binary_separated_merge_exchange`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Optimality.lower_split_merge_exchange`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Optimality.raw_terminal_bound`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Optimality.singleton_merge_cascade`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Optimality.terminal_raw_canonical`
- Dependency: [D5/S1/Digit/Carry/OrderedGame](../OrderedGame.md)
