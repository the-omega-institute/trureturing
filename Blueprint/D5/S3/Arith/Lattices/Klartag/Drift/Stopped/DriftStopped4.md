# Drift Stopped4

## Abstract

Stopped log determinant drift and integrability estimates.

Stopped log determinant drift and integrability estimates. The results below relate drift stopped4 to the stochastic ellipsoid construction.

**Theorem 1.1 (stopped Err split).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped4.stoppedErr_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped4.stoppedErr_split` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The two cases, kept apart. Each summand vanishes outside its own case, so the first sums by the freeze count and the second by the disjointness of {τ = k+1}.

**Definition 1.2 (Slack Hyp).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped4.SlackHyp`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped4.SlackHyp` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The numeric side condition the value of B closes: the middle case's total, C₁·2B, must fit the slack the existence step has. With C₁ ≤ 3n and B ≈ n^{−3.5} this is ≈ 6 n^{−2.5}.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped4.SlackHyp`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped4.stoppedErr_split`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ContactIntegrated](../../Contact/ContactIntegrated.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2](DriftStopped2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup](../../State/PaddedLawSetup.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StateInvariant4](../../State/StateInvariant4.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep](../../Tail/TailAtStep.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk](../../Walk/ChainWalk.md)
