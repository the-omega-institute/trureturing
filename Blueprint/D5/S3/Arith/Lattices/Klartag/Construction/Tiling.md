# Tiling

## Abstract

Construction A lattices, covolumes and ellipsoid transfer.

Construction A lattices, covolumes and ellipsoid transfer. The results below relate tiling to the stochastic ellipsoid construction.

**Definition 1.1 (to E).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.toE`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.toE` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The embedding ℤⁿ ↪ ℝⁿ (Euclidean).

**Definition 1.2 (cube).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.cube`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.cube` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The open unit cube centred at c.

**Theorem 1.3 (cube disjoint).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.cube_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.cube_disjoint` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Cubes centred at distinct integer points are disjoint.

**Theorem 1.4 (card le volume ball).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.card_le_volume_ball`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.card_le_volume_ball` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Cube packing. A finite set of integer points of norm ≤ R has cardinality at most the volume of the ball of radius R + √n/2.

**Theorem 1.5 (sum le lintegral).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.sum_le_lintegral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.sum_le_lintegral` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Sum-to-integral comparison (the cube-tiling lemma, in the form that needs no φ↑): a finite lattice sum is bounded by the integral of any function dominating it on each cube.

**Theorem 1.6 (abs coord le norm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.abs_coord_le_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.abs_coord_le_norm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A coordinate is bounded by the Euclidean norm.

**Theorem 1.7 (finite ball integer).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.finite_ball_integer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.finite_ball_integer` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Set finiteness. A Euclidean ball contains finitely many integer points.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.abs_coord_le_norm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.card_le_volume_ball`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.cube`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.cube_disjoint`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.finite_ball_integer`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.sum_le_lintegral`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Tiling.toE`
