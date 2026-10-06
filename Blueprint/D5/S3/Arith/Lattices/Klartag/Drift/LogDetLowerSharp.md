# Log Det Lower Sharp

## Abstract

Second order log determinant bounds and accumulated drift.

Second order log determinant bounds and accumulated drift. The results below relate log det lower sharp to the stochastic ellipsoid construction.

**Theorem 1.1 (log det one add ge sharp).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetLowerSharp.log_det_one_add_ge_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetLowerSharp.log_det_one_add_ge_sharp` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

LogDetVariance.log_det_one_add_ge with the sharp constant. The hypothesis is two-sided (|λ| ≤ r) where 94a's was one-sided (λ ≥ −1/2); the chain supplies it from the operator norm, which is what 94a's own proof already derived.

**Theorem 1.2 (log det add ge sharp).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetLowerSharp.log_det_add_ge_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetLowerSharp.log_det_add_ge_sharp` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

LogDetVariance.log_det_add_ge with the sharp constant.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetLowerSharp.log_det_add_ge_sharp`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetLowerSharp.log_det_one_add_ge_sharp`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/LogDetVariance](LogDetVariance.md)
