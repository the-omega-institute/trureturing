# Chain Drift

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate chain drift to the stochastic ellipsoid construction.

**Theorem 1.1 (telescope).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.telescope`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.telescope` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The telescoped drift bound. A one-step decrease with an error term sums to a bound on the terminal value. This is the discrete Riemann sum that replaces -(1/2)∫₀^T δ_s ds.

**Theorem 1.2 (integral le of cond Exp le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.integral_le_of_condExp_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.integral_le_of_condExp_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

If a conditional expectation is dominated a.e., the expectations are ordered.

**Theorem 1.3 (integral step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.integral_step`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.integral_step` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

One step, integrated.

**Theorem 1.4 (drift bound).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.drift_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.drift_bound` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The telescoped drift bound, integrated (Klartag Lemma 3.3, discrete form).

**Definition 1.5 (horizon).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.horizon`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.horizon` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

T = 16 log n / n² (Klartag Lemma 5.2, p. 23).

**Definition 1.6 (step Size).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.stepSize`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.stepSize` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

h = T / N, so that N·h = T exactly.

**Theorem 1.7 (step Size le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.stepSize_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.stepSize_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

h ≤ n^{-(e+2)}: the step size the choice of numSteps delivers.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.drift_bound`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.horizon`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.integral_le_of_condExp_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.integral_step`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.stepSize`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.stepSize_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.telescope`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/Chain](Chain.md)
