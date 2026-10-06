# Stopped Shortfall

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate stopped shortfall to the stochastic ellipsoid construction.

**Theorem 1.1 (sum norm lift Step le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.sum_norm_liftStep_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.sum_norm_liftStep_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

∑_{j<K} ‖ℓ_j‖ ≤ card(C_K)·η, the intermediate step of LiftBound.norm_liftSum_le_card.

**Theorem 1.2 (sum sq le sq sum).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.sum_sq_le_sq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.sum_sq_le_sq_sum` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A sum of squares of non-negatives is at most the square of the sum.

**Theorem 1.3 (sum lift Step sq le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.sum_liftStep_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.sum_liftStep_sq_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

∑_{j<K} ‖ℓ_j‖² ≤ (c₃η)² on a path whose count stays below c₃.

**Theorem 1.4 (norm gauss Step sq le trunc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.norm_gaussStep_sq_le_trunc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.norm_gaussStep_sq_le_trunc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

‖π_jξ_j‖² ≤ min(‖ξ_j‖², η²) whenever the raw step is capped by η.

**Theorem 1.5 (log Det stopped ge final).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.logDet_stopped_ge_final`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.logDet_stopped_ge_final` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The pathwise lower bound ShortfallBound.shortfall_le consumes. M is LogDetMartingale.mgPart … K, whose second moment is variance_M_le; D is a non-negative multiple of the truncated chi-square sum, a constant, and MidTerm.midCap, all three measurable with deterministic ranges.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.logDet_stopped_ge_final`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.norm_gaussStep_sq_le_trunc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.sum_liftStep_sq_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.sum_norm_liftStep_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.sum_sq_le_sq_sum`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/MidTerm](../Tail/MidTerm.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance](StepTruncVariance.md)
