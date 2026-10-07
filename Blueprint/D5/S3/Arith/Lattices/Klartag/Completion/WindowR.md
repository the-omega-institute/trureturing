# Window R

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate window r to the stochastic ellipsoid construction.

**Definition 1.1 (m R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.mR`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.mR` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The adopted lower bound on the state's quadratic form, DriftStopped6.mAdopted.

**Theorem 1.2 (log le four qrt).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.log_le_four_qrt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.log_le_four_qrt` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

log n ≤ 4·n^{1/4}, from log x ≤ x − 1 at x = n^{1/4}.

**Theorem 1.3 (qrt ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.qrt_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.qrt_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

√√n ≥ 37 at the threshold (√√2 073 600 = 37.947).

**Theorem 1.4 (log mul le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.log_mul_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.log_mul_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

9216·log n ≤ n at the threshold.

**Theorem 1.5 (m R ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.mR_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.mR_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

window_small at the reach: mR n ≥ a0C n − 1/2.

**Definition 1.6 (YR).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.YR`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.YR` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The y-endpoint of the reach window: YR n·√T = a0C n − mR n, identically in t.

**Definition 1.7 (reach Num).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.reachNum`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.reachNum` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The reach window's numerator: windowR α n = reachNum n/α + √n/2 by rfl.

**Definition 1.8 (window R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.windowR`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.windowR` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The reach window.

**Theorem 1.9 (sqrt T mul YR).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.sqrtT_mul_YR`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.sqrtT_mul_YR` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

√T·YR = a0C − mR, the identity that makes window_small t-free.

**Theorem 1.10 (reach Num eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.reachNum_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.reachNum_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

reachNum = 1/√(mR).

**Theorem 1.11 (window R lt p).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.windowR_lt_p`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.windowR_lt_p` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

window_lt_p at the reach: 2·reachNum n ≤ α·p and α·√n ≤ 1 give windowR α n < p.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.YR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.log_le_four_qrt`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.log_mul_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.mR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.mR_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.qrt_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.reachNum`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.reachNum_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.sqrtT_mul_YR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.windowR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR.windowR_lt_p`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6](../Drift/Stopped/DriftStopped6.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3](../Gaussian/GaussianMaximal3.md)
