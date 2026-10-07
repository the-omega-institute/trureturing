# Chain Ellipsoid

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate chain ellipsoid to the stochastic ellipsoid construction.

**Definition 1.1 (ellipsoid).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.ellipsoid`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.ellipsoid` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

E_A = {v | ⟪A v, v⟫ < 1}, Klartag eq. (9).

**Theorem 1.2 (det sq mul det).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.det_sq_mul_det`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.det_sq_mul_det` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Sᵀ A S = 1 forces det(S)² det(A) = 1; in particular S is invertible.

**Theorem 1.3 (quad congr).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.quad_congr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.quad_congr` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The congruence identity for the quadratic form.

**Theorem 1.4 (image ball eq ellipsoid).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.image_ball_eq_ellipsoid`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.image_ball_eq_ellipsoid` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Klartag eq. (9): the ellipsoid is the image of the unit ball.

**Theorem 1.5 (volume ellipsoid).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.volume_ellipsoid`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.volume_ellipsoid` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Klartag eq. (10): Vol(E_A) = det(A)^{-1/2} Vol(Bⁿ).

**Theorem 1.6 (volume ellipsoid ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.volume_ellipsoid_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.volume_ellipsoid_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Klartag eq. (68). If √(det A) · D ≤ Vol(Bⁿ) then the ellipsoid has volume at least D. The chain supplies det A_T ≤ C/n⁴, i.e. D = c n².

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.det_sq_mul_det`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.ellipsoid`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.image_ball_eq_ellipsoid`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.quad_congr`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.volume_ellipsoid`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.volume_ellipsoid_ge`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/Scaling](../Construction/Scaling.md)
