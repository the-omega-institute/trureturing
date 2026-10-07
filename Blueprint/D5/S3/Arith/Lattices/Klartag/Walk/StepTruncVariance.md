# Step Trunc Variance

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate step trunc variance to the stochastic ellipsoid construction.

**Definition 1.1 (sq Trunc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.sqTrunc`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.sqTrunc` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The truncated squared step norm.

**Theorem 1.2 (mem Lp sq Trunc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.memLp_sqTrunc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.memLp_sqTrunc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

MemLp _ 2, from the cap.

**Theorem 1.3 (pairwise indep Fun sq Trunc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.pairwise_indepFun_sqTrunc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.pairwise_indepFun_sqTrunc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Independence across steps, carried through the truncation by IndepFun.comp.

**Theorem 1.4 (variance sum sq Trunc le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.variance_sum_sqTrunc_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.variance_sum_sqTrunc_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The variance of the truncated drift proxy, K·cap²/4. At the adopted parameters cap = η² and this is N·η⁴/4 = T·h·dim²·n², about 4·log n·n⁻⁵.

**Theorem 1.5 (integrable sum sq Trunc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.integrable_sum_sqTrunc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.integrable_sum_sqTrunc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The truncated drift proxy is bounded, hence integrable.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.integrable_sum_sqTrunc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.memLp_sqTrunc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.pairwise_indepFun_sqTrunc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.sqTrunc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.variance_sum_sqTrunc_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/DriftVarianceBounded](../Drift/DriftVarianceBounded.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup](ChainSetup.md)
