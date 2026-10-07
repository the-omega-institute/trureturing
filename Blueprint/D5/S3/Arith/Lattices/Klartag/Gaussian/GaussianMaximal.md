# Gaussian Maximal

## Abstract

Gaussian moments, independence and operator norm tails.

Gaussian moments, independence and operator norm tails. The results below relate gaussian maximal to the stochastic ellipsoid construction.

**Definition 1.1 (max Norm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.maxNorm`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.maxNorm` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The running maximum of the increments' norms.

**Theorem 1.2 (le max Norm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.le_maxNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.le_maxNorm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Every increment before N is below the maximum — the pointwise fact the stopping-time corollary runs on.

**Theorem 1.3 (norm at index le max Norm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.norm_at_index_le_maxNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.norm_at_index_le_maxNorm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The stopping-time corollary. For any index function τ with τ ω < N, the increment read at τ is below the maximum, pointwise — so its expectation is too.

**Theorem 1.4 (exists le of lt max Norm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.exists_le_of_lt_maxNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.exists_le_of_lt_maxNorm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

If the running maximum exceeds a non-negative level, some increment does.

**Theorem 1.5 (max Norm tail).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.maxNorm_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.maxNorm_tail` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The maximum's tail, normalised. With σ² = v·d the union bound over the N steps and the d coordinates gives a *standard* Gaussian tail in t.

**Theorem 1.6 (lintegral max Norm le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.lintegral_maxNorm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.lintegral_maxNorm_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The maximal inequality, in lintegral form. No integrability hypothesis.

**Theorem 1.7 (expectation max norm le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.expectation_max_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.expectation_max_norm_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The maximal inequality, in Bochner form.

**Theorem 1.8 (expectation max norm le log).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.expectation_max_norm_le_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.expectation_max_norm_le_log` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The maximal inequality with the level chosen. At a = √(2·log K) with K = 2dN, the tail term is exactly σ/a ≤ σ, so E[max_{k<N} ‖ξ_k‖] ≤ σ·(√(2·log(2dN)) + 1), σ = √(v·d). The only size condition is K ≥ e, which holds as soon as there are two steps in dimension two.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.exists_le_of_lt_maxNorm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.expectation_max_norm_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.expectation_max_norm_le_log`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.le_maxNorm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.lintegral_maxNorm_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.maxNorm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.maxNorm_tail`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.norm_at_index_le_maxNorm`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail](../Tail/PaddedTail.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2](../Walk/StepInputs2.md)
