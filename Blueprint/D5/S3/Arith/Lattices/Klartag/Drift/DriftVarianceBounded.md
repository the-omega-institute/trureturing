# Drift Variance Bounded

## Abstract

Second order log determinant bounds and accumulated drift.

Second order log determinant bounds and accumulated drift. The results below relate drift variance bounded to the stochastic ellipsoid construction.

**Theorem 1.1 (variance trunc le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftVarianceBounded.variance_trunc_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftVarianceBounded.variance_trunc_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Popoviciu, per summand.

**Theorem 1.2 (variance sum le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftVarianceBounded.variance_sum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftVarianceBounded.variance_sum_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The drift proxy's variance, from independence and a pathwise cap. No Gaussian moment of any order is used.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftVarianceBounded.variance_sum_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftVarianceBounded.variance_trunc_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound](../Completion/ShortfallBound.md)
