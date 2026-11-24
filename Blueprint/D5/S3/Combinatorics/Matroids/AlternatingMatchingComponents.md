# Components of Two Perfect Matchings

## Abstract

The component of two perfect matchings is a square exactly at their commuting vertices.

**Definition 1.1 (Distinct matching partners).**

Lean statement: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.Matchings`

*Formalization.* `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.Matchings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two functions on the vertex type are involutions without fixed points and give distinct partners at each vertex.

**Definition 1.2 (Union graph).**

Lean statement: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.graph`

*Formalization.* `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.graph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An edge joins a vertex to either of its two partners.

**Theorem 1.3 (The component at a commuting vertex).**

Lean statement: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.component_eq_square`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.component_eq_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Where applying the two involutions in either order gives the same vertex, the component consists of the start, the two partners, and that common endpoint. These vertices are closed under both matchings and each is reachable from the start.

**Theorem 1.4 (Six vertices in a noncommuting component).**

Lean statement: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.six_le_component_of_noncommute`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.six_le_component_of_noncommute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite vertex type, disagreement between the two compositions gives at least six vertices in the component. The start, the two one-step endpoints, the two ordered two-step endpoints, and the endpoint of a first-second-first path are all distinct.

**Theorem 1.5 (Component size detects noncommutation).**

Lean statement: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.noncommute_iff_six_le_component`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.noncommute_iff_six_le_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite vertex type, the compositions disagree at the start if and only if its component has at least six vertices. In the commuting case the four enumerated vertices are distinct.

**Theorem 1.6 (A component of size at least six).**

Lean statement: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.exists_large_component_of_not_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.exists_large_component_of_not_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the number of vertices in a finite graph formed by the two matchings is not divisible by four, some component has at least six vertices. Otherwise the component sizes would all be four and would sum to a multiple of four.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.Matchings`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.component_eq_square`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.exists_large_component_of_not_dvd`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.graph`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.noncommute_iff_six_le_component`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents.six_le_component_of_noncommute`
