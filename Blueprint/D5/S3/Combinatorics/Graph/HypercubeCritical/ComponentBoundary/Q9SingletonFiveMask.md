# Double coverage on eight points and singleton masks in Q9

## Abstract

Tight Fano overlaps force a five-axis mask with a unique direction triple

**Theorem 1.1 (Double coverage on eight points requires at least thirteen triples).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask.thirteen_le_card_of_double_five_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask.thirteen_le_card_of_double_five_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a family of distinct triples on an eight-point set S. If every five-subset of S contains at least two members of F, then F has at least thirteen members.

Counting triple and five-set incidences gives an initial lower bound of twelve. With exactly twelve triples, at least four point deletions are tight, each leaving seven triples on seven points. In each tight restriction, every five-set contains exactly two triples. Counting in the six-point restrictions then gives exactly one triple through each pair, the Fano plane incidence law. Choose four tight deletion points. A pair meeting their complement survives at least three of these deletions, each leaving one triple through that pair. If one such deletion removed a triple through the pair, there would be exactly two original triples through it, and all three deletions would have to remove distinct triples through it. Hence any triple touching the four chosen points lies entirely among them. Each chosen point needs five triples through it, but only three triples among four points can contain a fixed point.

**Theorem 1.2 (A cover by at most nineteen triples has a singleton five-axis mask).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask.exists_singleton_five_mask`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask.exists_singleton_five_mask` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take at most nineteen distinct triples on the nine axes. If every five-axis mask contains a family member, some such mask contains exactly one. Otherwise each mask contains at least two. Each of the nine eight-axis restrictions would then contain at least thirteen triples, giving at least 117 incidences. Each triple survives six deletions, so nineteen triples give at most 114 incidences.

For a subcubic Q9 component, use the distinct incident direction sets of its degree-three vertices as the triple family. Under the coverage and size hypotheses, the chosen mask contains exactly one of those direction sets. This supplies the uniqueness hypothesis of the masked-face normal form, whose application also requires balance and singularity at the mask. The resulting conditional restriction concerns Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask.exists_singleton_five_mask`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask.thirteen_le_card_of_double_five_cover`
