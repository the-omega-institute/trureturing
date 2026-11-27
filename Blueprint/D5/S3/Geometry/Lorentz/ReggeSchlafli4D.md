# Euclidean Schläfli identity and Regge variation

## Abstract

Minkowski facet closure gives the Euclidean Schläfli identity and the first variation of the four-dimensional Regge action.

**Theorem 1.1 (Outward unit facet normals).**

Lean statement: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.facet_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.facet_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Regge (1961). *General Relativity without Coordinates*. URL: <https://doi.org/10.1007/BF02733251>.

*Commentary.*

The outward unit normal is the negative normalized gradient of the barycentric coordinate. The coordinate vanishes on the opposite facet and is one at its excluded vertex.

**Theorem 1.2 (Minkowski facet closure).**

Lean statement: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.facet_closure`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.facet_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Regge (1961). *General Relativity without Coordinates*. URL: <https://doi.org/10.1007/BF02733251>.

*Commentary.*

Each facet has positive Euclidean volume. By the base-and-height formula, its volume is the simplex volume times the dimension and the norm of its barycentric gradient. Summing the weighted normals gives zero because the barycentric coordinates sum to one.

**Theorem 1.3 (Interior dihedral cosine).**

Lean statement: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.dihedral_cosine`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.dihedral_cosine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Regge (1961). *General Relativity without Coordinates*. URL: <https://doi.org/10.1007/BF02733251>.

*Commentary.*

The cosine of the interior dihedral angle is the negative inner product of the outward unit normals. Projecting one gradient into the other facet gives a nonzero vector for distinct facets.

**Theorem 1.4 (Euclidean Schläfli differential identity).**

Lean statement: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.euclidean_schlafli`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.euclidean_schlafli` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Regge (1961). *General Relativity without Coordinates*. URL: <https://doi.org/10.1007/BF02733251>.

*Commentary.*

In every dimension at least two, differentiable vertex paths through nondegenerate simplices have zero sum of ridge volumes times interior dihedral angle derivatives. The base-and-height formula applied twice gives the ridge volume as the dimension times its predecessor, the simplex volume, the product of the gradient norms and the sine of the angle. The derivative of arccos cancels the sine. Contracting the differentiated normal inner products with the gradient norms then uses Minkowski facet closure. Unit norms give zero diagonal derivatives, and symmetry counts each distinct pair twice.

**Theorem 1.5 (Tetrahedron edge-length identity).**

Lean statement: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.tetrahedron_schlafli`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.tetrahedron_schlafli` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Regge (1961). *General Relativity without Coordinates*. URL: <https://doi.org/10.1007/BF02733251>.

*Commentary.*

In dimension three the ridges are edges and their volumes are the distances between their endpoints.

**Theorem 1.6 (Four-simplex triangle-area identity).**

Lean statement: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.four_simplex_schlafli`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.four_simplex_schlafli` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Regge (1961). *General Relativity without Coordinates*. URL: <https://doi.org/10.1007/BF02733251>.

*Commentary.*

In dimension four the ten ridges are triangles and their volumes are their Euclidean areas.

**Theorem 1.7 (First variation of the Regge action).**

Lean statement: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regge_variation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regge_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Regge (1961). *General Relativity without Coordinates*. URL: <https://doi.org/10.1007/BF02733251>.

*Commentary.*

Each four-simplex embeds its ten local triangles in the finite type of global hinges. Its triangle areas agree with the differentiable area functions on those hinges. A deficit is two pi minus the sum of incident interior dihedral angles. The product rule gives area and angle terms. Exchanging the finite sums groups the angle terms by simplex, where the four-simplex identity cancels each group. The derivative is the sum of each hinge area derivative times its deficit.

**Theorem 1.8 (Regular four-simplex edge length).**

Lean statement: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_edge_length`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_edge_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Regge (1961). *General Relativity without Coordinates*. URL: <https://doi.org/10.1007/BF02733251>.

*Commentary.*

The centered vertex Gram matrix has entries equal to half the squared edge length times a Kronecker delta minus one fifth of that factor. It yields the given positive length for every edge.

**Theorem 1.9 (Regular four-simplex dihedral angle).**

Lean statement: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_dihedral_angle`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_dihedral_angle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Regge (1961). *General Relativity without Coordinates*. URL: <https://doi.org/10.1007/BF02733251>.

*Commentary.*

The barycentric gradients are a common positive multiple of the centered vertices. Their normalized inner product is negative one quarter on distinct vertices, so the interior angle is arccos of one quarter. Minkowski facet closure applies to these same normals.

**Theorem 1.10 (Regular four-simplex triangle area).**

Lean statement: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_triangle_area`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_triangle_area` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Regge (1961). *General Relativity without Coordinates*. URL: <https://doi.org/10.1007/BF02733251>.

*Commentary.*

The perpendicular residual of the third vertex from an edge line has length square root of three times half the edge length. The triangle area is square root of three times one quarter of the squared edge length.

**Theorem 1.11 (Uniform dilation of the regular simplex).**

Lean statement: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_scaling_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_scaling_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Regge (1961). *General Relativity without Coordinates*. URL: <https://doi.org/10.1007/BF02733251>.

*Commentary.*

Multiplying the positive edge length by the exponential of time preserves the angle at every hinge. Each angle derivative vanishes along this path.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.dihedral_cosine`
- Truth anchor: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.euclidean_schlafli`
- Truth anchor: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.facet_closure`
- Truth anchor: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.facet_normal`
- Truth anchor: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.four_simplex_schlafli`
- Truth anchor: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regge_variation`
- Truth anchor: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_dihedral_angle`
- Truth anchor: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_edge_length`
- Truth anchor: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_scaling_cancellation`
- Truth anchor: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.regular_triangle_area`
- Truth anchor: `D5/S3/Geometry/Lorentz/ReggeSchlafli4D.tetrahedron_schlafli`
