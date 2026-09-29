# Pattern Constraints on Cycle Arcs

## Abstract

Avoidance of 1324 constrains the relative order of high and low arcs.

**Theorem 1.1 (No 213 in the rooted suffix).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns.rooted_suffix_avoids_213`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns.rooted_suffix_avoids_213` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

If a word beginning with one avoids 1324 and its remaining letters exceed one, that suffix contains no 213 subsequence.

**Theorem 1.2 (Separation of the arcs).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns.high_arc_above_low_arc`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns.high_arc_above_low_arc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

In a 1324-avoiding word beginning with one, every letter before two exceeds every letter after two when the prefix letters exceed two and all letters are distinct.

**Theorem 1.3 (Increasing low arc).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns.low_arc_has_no_descent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns.low_arc_has_no_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

If every rotation avoids 1324 and the letters after two lie below a nonempty high prefix, then the letters after two have no descent.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns.high_arc_above_low_arc`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns.low_arc_has_no_descent`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns.rooted_suffix_avoids_213`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicDefs](ArcherCyclicDefs.md)
