# Additively rigid vertex

## Abstract

Every finite subset of the edges incident to the vertex has a distinct sum of labels.

**Definition 1.1 (Additively rigid vertex).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.IsARVertex`

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.IsARVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every finite subset of the edges incident to the vertex has a distinct sum of labels.

**Definition 1.2 (Exact interval edge labeling).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.IsARGraph`

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.IsARGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The edge labels form a bijection onto the integers from one to the edge count, and every vertex is additively rigid.

**Theorem 1.3 (Cubic local criterion).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.ar_vertex_of_no_additive_relation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.ar_vertex_of_no_additive_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive distinct labels on a degree-three vertex give distinct subset sums whenever no two incident labels sum to the third.

**Theorem 1.4 (Cubic degree-sum identity).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.cubic_card_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.cubic_card_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three times the vertex count is twice the edge count by the degree-sum formula.

**Theorem 1.5 (Small orders and parity).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.cubic_order_constraints`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.cubic_order_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonempty simple cubic graph has at least four vertices and its vertex count is even.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.IsARGraph`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.IsARVertex`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.ar_vertex_of_no_additive_relation`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.cubic_card_identity`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.cubic_order_constraints`
