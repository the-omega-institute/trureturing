# Symmetric forms and the massive reference norm

## Abstract

Uniform comparison and the finite relative covariance trace in four dimensions.

**Definition 1.1 (Ambient symmetric covariance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.nullN`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.nullN` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Add the massive correction to the identity.

**Theorem 1.2 (Ambient coercivity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.nullN_coercive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.nullN_coercive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The Hilbert–Schmidt correction, injective skew multiplier and two signed positive bounds supply a strictly positive lower bound for the symmetric covariance.

**Definition 1.3 (Compressed covariance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.compressedN`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.compressedN` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Compress the ambient symmetric covariance by the inclusion of a complete complex subspace and its adjoint.

**Definition 1.4 (Massless symmetric square).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.mu0Sq`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.mu0Sq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take the squared norm of a vector in the subspace.

**Definition 1.5 (Massive symmetric square).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.mumSq`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.mumSq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take the real quadratic form of the compressed covariance.

**Theorem 1.6 (Upper comparison).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.mumSq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.mumSq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The operator norm of the ambient symmetric covariance bounds the massive square by the massless square, using the isometric inclusion and the inner product inequality.

**Definition 1.7 (Inverse covariance root).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.invRootN`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.invRootN` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take the ring inverse of the positive square root of the compressed covariance. Coercivity ensures that this square root is a unit.

**Definition 1.8 (Reference map).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.referenceMap`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.referenceMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Compose the subspace inclusion with the inverse covariance root.

**Definition 1.9 (Relative symmetric covariance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.relativeQ`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.relativeQ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Transport the identity by congruence with the reference map.

**Definition 1.10 (Relative skew form).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.relativeR`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.relativeR` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Transport the skew multiplier by congruence with the reference map and multiply by the imaginary unit.

**Definition 1.11 (Relative root difference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.eq71Delta`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.eq71Delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Subtract the positive covariance square roots in the massive reference representation.

**Theorem 1.12 (Uniform finite-trace bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.nullDiamond_eq71_4D`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.nullDiamond_eq71_4D` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For positive mass and length, a single positive lower comparison constant applies to all complete complex subspaces. The inverse root normalizes the massive symmetric covariance to the identity. The transported relative symmetric covariance is invertible with trivial kernel, both covariance operators are positive, and the quarter-power congruence estimate bounds the squared Hilbert–Schmidt norm of their root difference by the inverse comparison constant times the squared weighted correction norm.

**Theorem 1.13 (Literal operator trace).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.eq71_trace_eq_hsSq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.eq71_trace_eq_hsSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The difference of the two positive roots is self-adjoint and Hilbert–Schmidt. Its square is trace class. Evaluating the trace in a Hilbert basis gives the sum of squared image norms, equal to the squared Hilbert–Schmidt norm as a complex scalar.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.compressedN`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.eq71Delta`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.eq71_trace_eq_hsSq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.invRootN`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.mu0Sq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.mumSq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.mumSq_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.nullDiamond_eq71_4D`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.nullN`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.nullN_coercive`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.referenceMap`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.relativeQ`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.relativeR`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D](NullDiamondMultipliers4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPositivity4D](NullDiamondPositivity4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt](QuarterPowerSqrtHilbertSchmidt.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/GeneralIdeal](../TraceClass/GeneralIdeal.md)
