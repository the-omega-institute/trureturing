# A rational six-axis open cover

## Abstract

Six explicit rational axes cover the real unit two-sphere by relatively open orthogonality-free sets.

**Definition 1.1 (Real Euclidean three-space).**

Lean statement: `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.Space`

*Formalization.* `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.Space` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

The ambient space is EuclideanSpace over the reals indexed by Fin 3, with its standard Euclidean norm and inner product.

**Definition 1.2 (The standard unit two-sphere).**

Lean statement: `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.UnitSphere`

*Formalization.* `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.UnitSphere` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

The carrier is Metric.sphere zero one in EuclideanSpace over the reals indexed by Fin 3. It has the ordinary subspace topology and the standard real inner product.

**Definition 1.3 (The six rational axes).**

Lean statement: `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.axis`

*Formalization.* `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.axis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

In order, the six vectors are (1,2,0), (1,-2,0), (0,1,2), (0,1,-2), (2,0,1), and (-2,0,1). Each has squared Euclidean norm five. No normalization or choice of an irrational coordinate is required.

**Definition 1.4 (Strict projection superlevels).**

Lean statement: `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.color`

*Formalization.* `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.color` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

For each index i in Fin 6, the corresponding subset consists of all actual unit vectors x satisfying 5 < 2 times the square of the inner product of x with axis i. These are subsets of the entire sphere.

**Theorem 1.5 (An open orthogonality-free cover).**

Lean statement: `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.rational_six_axis_open_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.rational_six_axis_open_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

All six subsets are open in the sphere, each excludes every orthogonal pair of unit vectors, and their indexed union is the entire sphere. Openness follows from continuity of the inner product and the strict inequality. For orthogonal unit x and y, the two-vector Bessel inequality gives the sum of their squared projections onto any one axis at most five; membership of both would make that sum greater than five. The proof uses Mathlib's Orthonormal.sum_inner_products_le. For coverage put a=abs(x0), b=abs(x1), c=abs(x2), Q=a squared plus b squared plus c squared, and M=max(a+2b,b+2c,c+2a). Write u=M-a-2b, v=M-b-2c, and w=M-c-2a. All these quantities are nonnegative. The exact identity is 3 M squared - 9 Q = uv+vw+wu+6(aw+bu+cv)+((a-b) squared+(b-c) squared+(c-a) squared)/2. Thus M squared is at least 3 Q. One of the two signed forms for each coordinate pair has squared value (abs(s)+2 abs(t)) squared. Since Q=1 on the sphere, one of the six squared projections is at least three, which satisfies the strict threshold. This supplies the upper bound six for Feldman--Wilce Question 3. It proves no lower bound and does not determine higher-dimensional covering numbers. Feldman--Wilce supplies the question. The six-set upper bound has classical antecedents in antipodal icosahedral coverings, including Fowler, Tarnai and Gáspár, From circle packing to covering on a sphere with antipodal constraints (2002), DOI 10.1098/rspa.2002.0990. The rational coordinates and polynomial certificate describe this repository implementation; no mathematical novelty or priority is claimed.

## References

- Truth anchor: `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.Space`
- Truth anchor: `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.UnitSphere`
- Truth anchor: `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.axis`
- Truth anchor: `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.color`
- Truth anchor: `D5/S3/Geometry/Orthogonality/RationalSixAxisCover.rational_six_axis_open_cover`
