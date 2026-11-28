# Exact neighborhoods of dependent compositions

## Abstract

Exact neighborhoods of dependent compositions

A directed composition replaces each base edge by all edges between the corresponding clusters. The clusters may have different carriers and different internal graphs. Exact second neighbors exclude the root and its immediate outneighbors and require a two-edge witness. Walks include length zero.

**Theorem 1.1 (Asymmetry of the composition).**

Lean statement: `D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods.composition_asymm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods.composition_asymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arpan Sadhukhan; Sagnik Sen (2026). *Locating a Seymour vertex in oriented graphs having minimum outdegree at most 7*. URL: <https://arxiv.org/abs/2606.30588v2>.

*Commentary.*

An asymmetric base and asymmetric internal relations give an asymmetric relation on the dependent sum of the cluster carriers.

**Theorem 1.2 (Exact second-neighbor decomposition).**

Lean statement: `D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods.composition_exact_second`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods.composition_exact_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arpan Sadhukhan; Sagnik Sen (2026). *Locating a Seymour vertex in oriented graphs having minimum outdegree at most 7*. URL: <https://arxiv.org/abs/2606.30588v2>.

*Commentary.*

When each cluster is nonempty and the base is asymmetric, exact second neighbors of a vertex consist of its internal exact second neighbors together with all vertices in clusters above exact second neighbors of its base vertex. A path using one internal and one cross edge ends in a first-neighbor cluster and is excluded. A path using two cross edges cannot return to its starting cluster.

**Theorem 1.3 (Cardinalities of the disjoint pieces).**

Lean statement: `D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods.composition_degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods.composition_degrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arpan Sadhukhan; Sagnik Sen (2026). *Locating a Seymour vertex in oriented graphs having minimum outdegree at most 7*. URL: <https://arxiv.org/abs/2606.30588v2>.

*Commentary.*

For a finite base and finite nonempty cluster carriers, if the base is asymmetric and its vertex has a unique first-neighbor cluster s and a unique exact second-neighbor cluster t, the global first degree is its internal first degree plus the cardinality of s, and its global exact second degree is its internal exact second degree plus the cardinality of t.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods.composition_asymm`
- Truth anchor: `D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods.composition_degrees`
- Truth anchor: `D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods.composition_exact_second`
