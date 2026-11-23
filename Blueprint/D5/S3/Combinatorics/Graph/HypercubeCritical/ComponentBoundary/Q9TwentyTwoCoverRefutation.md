# Pair and five-set coverage on nine axes

## Abstract

A twenty-two-triple obstruction to the singleton-mask argument

**Definition 1.1 (A proposed singleton-mask criterion at twenty-two triples).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposed criterion asks whether twenty-two distinct triples on nine axes must singly cover some five-set whenever every pair and every five-set are covered.

**Theorem 1.2 (A pair-covering family doubles every five-set).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lean checks that the displayed family has exactly twenty-two triples, that all 36 pairs extend to a triple, and that all 126 five-sets contain at least two triples. This refutes the proposed criterion.

The witness concerns the necessary direction-cover conditions. Its realization as directions of a universally saturated component is a separate question. Hong, Wu and Xia ask whether f₂(Q₉) equals three or four. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation.result`
- Narrative reference: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage](Q9DirectionCoverage.md)
- Narrative reference: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover](Q9SharpDoubleFiveCover.md)
