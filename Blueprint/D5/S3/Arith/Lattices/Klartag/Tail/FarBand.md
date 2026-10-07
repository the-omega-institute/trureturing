# Far Band

## Abstract

Lattice tail bounds along the matrix walk.

Lattice tail bounds along the matrix walk. The results below relate far band to the stochastic ellipsoid construction.

**Theorem 1.1 (integrand le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/FarBand.integrand_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/FarBand.integrand_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Φ(y)·(1 − y·s)^{−c} ≤ e^{b·y − a·y²}/(√(2π)·Y₀) on y ≥ Y₀ > 0 with y·s ≤ 1/2, b = c·s, a = 1/2 − c·s².

**Theorem 1.2 (far le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/FarBand.far_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/FarBand.far_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The far-band bound. Y₀ is the split point, Y₁ the reach endpoint.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/FarBand.far_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/FarBand.integrand_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/WindowR](../Completion/WindowR.md)
