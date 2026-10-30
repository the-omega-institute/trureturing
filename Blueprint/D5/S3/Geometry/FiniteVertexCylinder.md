# Homotopy extension at a realized vertex

## Abstract

A division-free vertex-cylinder retraction and homotopy extension for finite coordinate realizations.

**Definition 1.1 (An actual realized vertex).**

Lean statement: `D5/S3/Geometry/FiniteVertexCylinder.vertexPoint`

*Formalization.* `D5/S3/Geometry/FiniteVertexCylinder.vertexPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let M be a pre-abstract simplicial complex on a finite ambient vertex type V. A singleton face {v} determines the coordinate vertex with entry one at v and zero elsewhere, as a point of the existing geometric realization of M. Vertices absent from M need not be realized.

**Definition 1.2 (The bottom and vertex cylinder).**

Lean statement: `D5/S3/Geometry/FiniteVertexCylinder.Cylinder`

*Formalization.* `D5/S3/Geometry/FiniteVertexCylinder.Cylinder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Inside the realization times the unit interval, the boundary subspace consists exactly of pairs whose time is zero or whose spatial coordinate is the chosen realized vertex.

**Definition 1.3 (A continuous coordinate retraction).**

Lean statement: `D5/S3/Geometry/FiniteVertexCylinder.retraction`

*Formalization.* `D5/S3/Geometry/FiniteVertexCylinder.retraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a point x and time t, write s=x_v and b=t s. Replace every coordinate x_w with w different from v by max(x_w-b,0), and assign the remaining mass to coordinate v. The new height is max(b+s-1,0). All new coordinates are nonnegative and sum to one. If the original face omits v, then s=0 and the point is unchanged; otherwise the new support stays in that face. A positive new height forces every coordinate other than v to vanish. Finite sums and maxima make both components jointly continuous, without division or a nonempty-link assumption.

**Theorem 1.4 (The boundary is fixed pointwise).**

Lean statement: `D5/S3/Geometry/FiniteVertexCylinder.retraction_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexCylinder.retraction_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continuous map to the bottom-or-vertex cylinder restricts to the identity on that entire subspace. At time zero the spatial point is unchanged and the new height is zero; at the chosen vertex the spatial point remains the vertex and the new height is the original time. Singleton complexes are included.

**Theorem 1.5 (Arbitrary target-valued homotopy extension).**

Lean statement: `D5/S3/Geometry/FiniteVertexCylinder.vertex_homotopy_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexCylinder.vertex_homotopy_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every topological space Y, every continuous map f from the finite coordinate realization to Y, and every continuous path h in Y starting at f(v), there is a jointly continuous map F on the realization times the unit interval satisfying F(x,0)=f(x) for all x and F(v,t)=h(t) for all t. The boundary map glues f and h along two closed sets and then composes with the explicit retraction. No separation property of Y is required. This establishes homotopy extension at each actual vertex; it does not assert homotopy extension for arbitrary subcomplexes or settle the remaining graph and join steps of Question 22.

## References

- Truth anchor: `D5/S3/Geometry/FiniteVertexCylinder.Cylinder`
- Truth anchor: `D5/S3/Geometry/FiniteVertexCylinder.retraction`
- Truth anchor: `D5/S3/Geometry/FiniteVertexCylinder.retraction_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteVertexCylinder.vertexPoint`
- Truth anchor: `D5/S3/Geometry/FiniteVertexCylinder.vertex_homotopy_extension`
- Dependency: [D5/S3/Geometry/FiniteConeCollapse](FiniteConeCollapse.md)
