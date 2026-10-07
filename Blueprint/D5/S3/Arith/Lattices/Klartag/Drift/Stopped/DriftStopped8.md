# Drift Stopped8

## Abstract

Stopped log determinant drift and integrability estimates.

Stopped log determinant drift and integrability estimates. The results below relate drift stopped8 to the stochastic ellipsoid construction.

**Theorem 1.1 (quad eq inner).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.quad_eq_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.quad_eq_inner` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The ellipsoid's quadratic form as an inner product, so StateBounds.lower applies to it.

**Theorem 1.2 (norm lt reach).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.norm_lt_reach`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.norm_lt_reach` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The reach. StateBounds A m M bounds the ellipsoid inside the ball of radius 1/√m: m‖v‖² ≤ ⟪v, Av⟫ < 1.

**Theorem 1.3 (not Mem ellipsoid of reach).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.notMem_ellipsoid_of_reach`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.notMem_ellipsoid_of_reach` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A lattice point at or beyond the reach is outside the ellipsoid, with no counting at all.

**Theorem 1.4 (not Mem ellipsoid of mem k Set).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.notMem_ellipsoid_of_mem_kSet`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.notMem_ellipsoid_of_mem_kSet` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The shell case, and it needs no probabilistic input. Chain.kSet is the set of matrices whose ellipsoid misses the window, and Chain.chain_fst_mem_kSet keeps the chain inside it at every step and on every path.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.norm_lt_reach`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.notMem_ellipsoid_of_mem_kSet`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.notMem_ellipsoid_of_reach`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.quad_eq_inner`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Theorem2](../../Completion/Theorem2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/LatticeData](../../Construction/LatticeData.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped7](DriftStopped7.md)
