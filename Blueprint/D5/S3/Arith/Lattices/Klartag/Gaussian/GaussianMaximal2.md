# Gaussian Maximal2

## Abstract

Gaussian moments, independence and operator norm tails.

Gaussian moments, independence and operator norm tails. The results below relate gaussian maximal2 to the stochastic ellipsoid construction.

**Theorem 1.1 (max Norm sq tail).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.maxNorm_sq_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.maxNorm_sq_tail` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The square's tail is exponential: P{maxNorm²/(2σ²) > t} ≤ 2dN·e^{−t}.

**Theorem 1.2 (lintegral max Norm sq le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.lintegral_maxNorm_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.lintegral_maxNorm_sq_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The second moment, in lintegral form.

**Theorem 1.3 (expectation max norm sq le log).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.expectation_max_norm_sq_le_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.expectation_max_norm_sq_le_log` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The second moment, in Bochner form, at the optimal level a = log(2dN).

**Theorem 1.4 (measurable at index).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.measurable_at_index`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.measurable_at_index` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

An increment read at a measurable random index is measurable: ℕ is countable.

**Definition 1.5 (Integrable At Index).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.IntegrableAtIndex`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.IntegrableAtIndex` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Both moments at a random index are integrable. Domination by maxNorm and maxNorm².

**Theorem 1.6 (maximal Hyp2 of laws).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.maximalHyp2_of_laws`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.maximalHyp2_of_laws` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

DriftStopped4.MaximalHyp2, both moments, with one constant.

**Theorem 1.7 (maximal At Adopted step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.maximalAtAdopted_step`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.maximalAtAdopted_step` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

DriftStopped4.MaximalAtAdopted at the drift lane's own increments. ChainSetup.step c is c • coord k, whose coordinates are N(0, c²) by ChainSetup.step_coord_law; so v = c² and σ = c·√d with d = card (UT n).

**Theorem 1.8 (six le log).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.six_le_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.six_le_log` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

log n ≥ 6 at the gate's threshold: e⁶ < 404 < 2 073 600.

**Theorem 1.9 (sqrt log majorant).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.sqrt_log_majorant`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.sqrt_log_majorant` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The majorant. √(2·log K) + 1 ≤ 5·√(log n) whenever log K ≤ 10·log n + 3 and log n ≥ 6. The slack is real but not large: at n = 2 073 600 the left side is 17.51 and the right 19.07.

**Theorem 1.10 (log two card num Steps le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.log_two_card_numSteps_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.log_two_card_numSteps_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

log (2·d·N) ≤ 10·log n + 3 at the adopted parameters: d ≤ n² and N = ⌈16·n⁷·log n⌉ ≤ 17·n⁷·log n, so 2dN ≤ 34·n⁹·log n, and log 34 ≤ 4, log (log n) ≤ log n − 1.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.IntegrableAtIndex`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.expectation_max_norm_sq_le_log`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.lintegral_maxNorm_sq_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.log_two_card_numSteps_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.maxNorm_sq_tail`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.maximalAtAdopted_step`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.maximalHyp2_of_laws`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.measurable_at_index`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.six_le_log`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.sqrt_log_majorant`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ContactIntegrated](../Contact/ContactIntegrated.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2](../Drift/Stopped/DriftStopped2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped4](../Drift/Stopped/DriftStopped4.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal](GaussianMaximal.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup](../State/PaddedLawSetup.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StateInvariant4](../State/StateInvariant4.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StepGlue](../State/StepGlue.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep](../Tail/TailAtStep.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup](../Walk/ChainSetup.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk](../Walk/ChainWalk.md)
