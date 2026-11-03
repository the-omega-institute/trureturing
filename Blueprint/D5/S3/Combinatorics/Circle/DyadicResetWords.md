# Realizing allocated coins as actual legal reset words

## Abstract

Realizing allocated coins as actual legal reset words.

**Theorem 1.1 (Realizing allocated coins as actual legal reset words).**

Lean statement: `D5/S3/Combinatorics/Circle/DyadicResetWords.word_of_allocation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/DyadicResetWords.word_of_allocation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a finite physical set of positive labels with f(a)=2^e(a), and let Z be an actual list of reset labels of value -M. For a natural tail h<=M, an Allocation into one capacity-M bin per occurrence of Z and one capacity-h tail produces a word V permuting S.toList++Z and satisfying InStrip(f,M,0,V). The construction concatenates each allocated positive list with its own actual reset occurrence and then the tail. Empty bins and a zero tail are included.

Positive monotonicity bounds every interior prefix by the exact bin endpoint. Each reset returns M to zero, and every tail prefix stays between zero and h. Physical disjointness of the allocation and the original reset list is retained through the permutation; it is never replaced by an inventory of numerical values.

allocation_of_strip derives the old positive set, actual reset list, endpoint and allocation from an arbitrary Nodup legal word using reset_decomposition. replace_bin removes a physical subcollection from a single bin and replaces it by a fresh coin of exactly its total, preserving all capacities. replacement_perm proves the exact returned/inserted physical permutation. top_occupancy counts each original top label exactly once and bounds a bin below twice the top denomination by one top occurrence; missing_top_bound supplies the exhaustive native case split.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/DyadicResetWords.word_of_allocation`
- Dependency: [D5/S3/Combinatorics/Circle/DyadicResetBlocks](DyadicResetBlocks.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeBitSource](ThreeBitSource.md)
- Dependency: [D5/S3/Combinatorics/Transportation/DyadicAllocation](../Transportation/DyadicAllocation.md)
