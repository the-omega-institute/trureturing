# Drift Stopped5

## Abstract

Stopped log determinant drift and integrability estimates.

Stopped log determinant drift and integrability estimates. The results below relate drift stopped5 to the stochastic ellipsoid construction.

**Theorem 1.1 (mid iff).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5.mid_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5.mid_iff` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The middle case pins k to τ − 1. k < τ and ¬(k+1 ≤ τ−1) force τ−1 ≤ k < τ.

**Theorem 1.2 (sum mid eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5.sum_mid_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5.sum_mid_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Summing the middle term is a single evaluation.

**Theorem 1.3 (measurable tau).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5.measurable_tau`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5.measurable_tau` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

τ is measurable — it is a stopping time, so {τ ≤ k} is measurable for every k, and a ℕ-valued map with measurable sublevel sets is measurable.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5.measurable_tau`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5.mid_iff`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5.sum_mid_eq`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped4](DriftStopped4.md)
