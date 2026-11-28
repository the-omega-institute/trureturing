# A large colorable induced subgraph

## Abstract

Reciprocal degrees bound the size of a colorable induced subgraph.

**Theorem 1.1 (A large colorable induced subgraph).**

Lean statement: `D5/S3/Combinatorics/Graph/DeletionResilientCliques/ColorableInducedSubgraph.exists_colorable_induce_of_minDegree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DeletionResilientCliques/ColorableInducedSubgraph.exists_colorable_induce_of_minDegree` (`✓ std3`). ∎

*Citation.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

Let s be positive, and let G be a finite graph with minimum degree at least s − 1. Some vertex set X induces an s-colorable graph and has cardinality at least the sum, over all vertices v, of s divided by degree(v) + 1. In each total ordering, keep the vertices with fewer than s earlier neighbors. Greedy coloring works in the inherited order. In the closed neighborhood of v the ranks of v have equal multiplicities, by swapping two vertex positions. Averaging these finite counts gives the stated set.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DeletionResilientCliques/ColorableInducedSubgraph.exists_colorable_induce_of_minDegree`
