# Drift Stopped

## Abstract

Stopped log determinant drift and integrability estimates.

Stopped log determinant drift and integrability estimates. The results below relate drift stopped to the stochastic ellipsoid construction.

**Definition 1.1 (stopped Log Det).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.stoppedLogDet`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.stoppedLogDet` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

D^τ_k = log det A_{min k (τ−1)}.

**Definition 1.2 (stopped Sub).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.stoppedSub`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.stoppedSub` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

K^τ_k = F(C_k) before the stopping time and ⊥ after: the free subspace the drift's N_k and quadratic term read.

**Definition 1.3 (stopped V).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.stoppedV`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.stoppedV` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

V^τ_k = π_k(A_k⁻¹) before the stopping time and 0 after.

**Theorem 1.4 (integral err Cond).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.integral_errCond`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.integral_errCond` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The integral is unchanged — which is why substituting errCond for err leaves the drift bound's conclusion alone.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.integral_errCond`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.stoppedLogDet`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.stoppedSub`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.stoppedV`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup](../../Walk/ChainSetup.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain](../../Walk/StoppedChain.md)
