# Subcubic extensions of the literal three-leaf star

## Abstract

A degree-deletion bound for the 108-point star in the nine-cube

**Definition 1.1 (The support from census orbit 23).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.starSupport`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.starSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vacuum layer contains M. Each of the three singleton layers contains B union M. The base coordinates are the first six bits, so a vertex with base word x and layer z is encoded by x + 64z.

**Definition 1.2 (A proposed subcubic extension above 255 vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposed extension contains the specified star and has at most three neighbors within the extension at every vertex.

**Theorem 1.3 (Every subcubic extension has at most 255 vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The star is cubic on 108 vertices. A subcubic extension can add vertices only in the 186-point complement R of its closed neighborhood. For every v in R, let k(v) be its degree in R minus three, truncated at zero. If v is kept, at least k(v) of its neighbors must be deleted. If v is deleted, its own deletion supplies k(v) toward the same inequality.

The ten positive orbit multipliers assign the same nonnegative integer weight to every vertex row in each listed orbit. They select and scale 71 local degree inequalities. Symmetric adjacency lets the sum collect by deleted vertex. Each resulting coefficient is at most 192, and the weighted right-hand side is 7,320. Thus at least 39 vertices of R must be deleted, leaving at most 108 + 186 - 39 = 255 vertices.

Hong, Wu and Xia's Problem 2 asks whether f₂(Q₉) is three or four. The bound rules out this particular cubic support in a 258-vertex subcubic candidate. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.starSupport`
- Narrative reference: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentSaturation](Q9ComponentSaturation.md)
