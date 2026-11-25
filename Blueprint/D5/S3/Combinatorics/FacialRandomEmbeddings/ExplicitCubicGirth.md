# Explicit Cubic Graphs of Prescribed Girth

## Abstract

Three explicit residue-ring involutions give finite matching-colored cubic graphs of prescribed girth.

**Theorem 1.1 (An explicit cubic graph for every girth threshold).**

Lean statement: `D5/S3/Combinatorics/FacialRandomEmbeddings/ExplicitCubicGirth.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FacialRandomEmbeddings/ExplicitCubicGirth.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each integer g at least two, act on pairs over the residue ring modulo 5^g+1 by three involutions, and use their tagged permutation orbit as the vertex set. The three moves give the matching neighbors of the actual simple graph.

An integral separated-cone estimate keeps the second coordinate of every nonempty reduced word of length at most g strictly nonzero modulo 5^g+1. A short graph cycle would give a forbidden reduced word. The tag gives a bipartition; alternating two colors shows that no edge is a bridge. Two columns determine the permutation, and their determinant determines the tag, giving at most (5^g+1)^4 vertices.

The result formalizes this particular explicit family and its marked matching coordinates, not a new existence theorem or an optimal bound. Biggs, Constructions for Cubic Graphs with Large Girth (1998, DOI 10.37236/1386), surveys the established Cayley method and sharper constructions. No signed-density claim is made here.

## References

- Truth anchor: `D5/S3/Combinatorics/FacialRandomEmbeddings/ExplicitCubicGirth.result`
