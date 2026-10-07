# Final

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate final to the stochastic ellipsoid construction.

**Theorem 1.1 (abs coord le norm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Final.abs_coord_le_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Final.abs_coord_le_norm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Every coordinate of a Euclidean vector is bounded by its norm.

**Theorem 1.2 (integer Points ball).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Final.integerPoints_ball`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Final.integerPoints_ball` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The unit ball has no non-zero integer point — the open cube (−1,1)^N contains it, and an integer of absolute value < 1 is 0.

**Definition 1.3 (ball Vol).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Final.ballVol`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/Final.ballVol` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Vol(B^N) as a real number.

**Definition 1.4 (small Const).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Final.smallConst`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/Final.smallConst` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

c₁ = min_{1 ≤ m < n₁} Vol(B^{m+1}) / m², a minimum over a finite set.

**Theorem 1.5 (small volume ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Final.small_volume_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Final.small_volume_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The small-dimension bound in the form klartag_of_volume_ge consumes.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Final.abs_coord_le_norm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Final.ballVol`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Final.integerPoints_ball`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Final.smallConst`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Final.small_volume_ge`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Assembly](Assembly.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/Scaling](../Construction/Scaling.md)
