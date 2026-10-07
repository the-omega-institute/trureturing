# Drift Stopped6

## Abstract

Stopped log determinant drift and integrability estimates.

Stopped log determinant drift and integrability estimates. The results below relate drift stopped6 to the stochastic ellipsoid construction.

**Theorem 1.1 (le eigenvalues of lower).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.le_eigenvalues_of_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.le_eigenvalues_of_lower` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Every eigenvalue is at least the quadratic form's lower bound. The companion of GoodEvent.abs_eigenvalues_le_opNorm, which the tree has and which supplies the upper bound; this direction is stated nowhere.

**Theorem 1.2 (det bounds of state Bounds).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.det_bounds_of_stateBounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.det_bounds_of_stateBounds` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

StateBounds is a two-sided determinant bound. m ≤ λᵢ ≤ M for every eigenvalue, so mⁿ ≤ det A ≤ Mⁿ. This is what makes log det of the stopped state a bounded function.

**Theorem 1.3 (continuous sym Mat det).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.continuous_symMat_det`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.continuous_symMat_det` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

symMat is linear in the Frobenius coordinates and det is a polynomial, so the composite is continuous — the route to measurability of logDet.

**Theorem 1.4 (measurable stopped Log Det).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.measurable_stoppedLogDet`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.measurable_stoppedLogDet` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

stoppedLogDet is measurable. min k (τ − 1) takes values in {0, …, k}, so the stopped state is a finite sum of indicators of the fibres of a measurable ℕ-valued map.

**Theorem 1.5 (integrable stopped Log Det).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.integrable_stoppedLogDet`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.integrable_stoppedLogDet` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

intD, the drift's first integrability field. stateBounds_stopped holds for every k and every ω, so the stopped log-determinant is bounded between n·log m and n·log M.

**Theorem 1.6 (integrable stopped Free Dim).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.integrable_stoppedFreeDim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.integrable_stoppedFreeDim` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

intN, the drift's second integrability field — free, as it is for the unstopped chain (ChainWiring.integrable_freeDim): the free dimension never exceeds dim E.

**Definition 1.7 (r0Adopted).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.r0Adopted`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.r0Adopted` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

r₀ at the adopted parameters: the good event's operator-norm threshold 6√(T·n), which GoodEvent.lean:320 evaluates to 24√(log n / n).

**Definition 1.8 (eta Adopted).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.etaAdopted`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.etaAdopted` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

η at the adopted parameters: √(2 h d n) with h = ParamsAdopted2.stepSizeAdopted2 n; ParamsAdopted2.eta2_le bounds it by √2 · n⁻³.

**Definition 1.9 (m Adopted).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.mAdopted`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.mAdopted` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

m_adopted: the state's lower bound a₀ − (r₀ + c₃η), SlackHyp's first free argument. a₀ = (1 − 1/n)⁻² is D5.S3.Arith.Lattices.Klartag.a0C (Lemma43Uniform.lean:431).

**Definition 1.10 (MAdopted).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.MAdopted`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.MAdopted` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The state's upper bound M = a₀ + (r₀ + c₃η).

**Definition 1.11 (delta Adopted).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.deltaAdopted`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.deltaAdopted` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

δ = η / m, the smallest value DriftStopped.hpt_stopped's hδ admits.

**Definition 1.12 (c Adopted).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.cAdopted`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.cAdopted` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

c_adopted: the drift's quadratic coefficient 1 / (2 M² (1+δ)²), SlackHyp's second free argument — the c at which DriftStopped.hpt_stopped is stated.

**Definition 1.13 (slack Adopted).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.slackAdopted`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.slackAdopted` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

slack_adopted: the slack the middle case must fit into, of order 1.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.MAdopted`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.cAdopted`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.continuous_symMat_det`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.deltaAdopted`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.det_bounds_of_stateBounds`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.etaAdopted`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.integrable_stoppedFreeDim`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.integrable_stoppedLogDet`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.le_eigenvalues_of_lower`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.mAdopted`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.measurable_stoppedLogDet`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.r0Adopted`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.slackAdopted`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5](DriftStopped5.md)
