# Shortest distances in a once-subdivided complete graph

## Abstract

Shortest distances in a once-subdivided complete graph

The graph has all n original vertices and one midpoint for every unordered pair of distinct originals. Only original-to-incident-midpoint pairs are adjacent. This is the once-subdivision of every edge of the complete graph, as defined on printed page 21 of the cited versioned source. Reachability is proved before natural-valued graph distances are used.

**Definition 1.1 (Midpoint).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.Midpoint`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.Midpoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Unordered pairs of distinct original vertices label exactly one inserted vertex per complete-graph edge.

**Definition 1.2 (Vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.Vertex`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The full finite vertex type is the disjoint union of originals and all inserted midpoints.

**Definition 1.3 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.graph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Adjacency holds exactly between an original vertex and a midpoint containing it.

**Definition 1.4 (subdivisionVertex).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.subdivisionVertex`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.subdivisionVertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Distinct original endpoints determine their single unordered midpoint.

**Theorem 1.5 (midpoint swap).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.midpoint_swap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.midpoint_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Exchanging the original endpoints preserves their midpoint.

**Theorem 1.6 (adj original midpoint).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.adj_original_midpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.adj_original_midpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Original-to-midpoint adjacency is exactly membership in the underlying unordered pair.

**Theorem 1.7 (reachable).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.reachable`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Every pair of actual graph vertices is joined by a walk.

**Theorem 1.8 (dist original original).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.dist_original_original`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.dist_original_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Original vertices have shortest distance zero when equal and two when distinct.

**Theorem 1.9 (dist original midpoint).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.dist_original_midpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.dist_original_midpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

An original vertex has shortest distance one to an incident midpoint and three to a nonincident midpoint.

**Theorem 1.10 (dist midpoint midpoint).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.dist_midpoint_midpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.dist_midpoint_midpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Midpoints have shortest distance zero when equal, two when distinct with a common endpoint, and four when disjoint.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.Midpoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.adj_original_midpoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.dist_midpoint_midpoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.dist_original_midpoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.dist_original_original`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.midpoint_swap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.reachable`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.subdivisionVertex`
