# Powers–Størmer and trace-class stability of square roots

## Abstract

The constant-one trace-norm inequality holds on every complex Hilbert space. It controls the trace-class terms in a covariance perturbation before and after bounded congruence.

**Theorem 1.1 (Compact square-root difference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.isCompactOperator_sqrt_sub_of_isCompactOperator_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.isCompactOperator_sqrt_sub_of_isCompactOperator_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Uniform real polynomial approximation on a common spectral interval gives operator-norm convergence. Each polynomial difference lies in the compact ideal by telescoping the differences of powers.

**Theorem 1.2 (Hilbert–Schmidt root difference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.powers_stormer_isHilbertSchmidt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.powers_stormer_isHilbertSchmidt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

In the real eigenbasis of the compact self-adjoint root difference, each squared eigenvalue is bounded by the modulus of the corresponding diagonal entry of the covariance difference.

**Theorem 1.3 (Powers–Størmer inequality).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.powers_stormer_hsSq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.powers_stormer_hsSq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Sum the diagonal bound in the eigenbasis and use the trace-norm bound for the diagonal pairing with the identity.

**Theorem 1.4 (Equality on the complex line).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.powers_stormer_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.powers_stormer_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The positive operators zero and identity on the complex line have a squared Hilbert–Schmidt root difference and a trace-norm difference both equal to one.

**Theorem 1.5 (Trace-class correction to the quarter-power bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.quarterPower_add_traceClass_sqrt_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.quarterPower_add_traceClass_sqrt_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Add the absolute value of the self-adjoint correction to the reference, and its absolute value minus itself to the target. Both shifts are positive trace class. The squared estimate is three times the sum of the squared Hilbert–Schmidt factor and three times the trace norm of the correction.

**Theorem 1.6 (Bounded congruence of the perturbation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.quarterPower_add_traceClass_congruence_sqrt_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.quarterPower_add_traceClass_congruence_sqrt_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The congruence may act between different Hilbert spaces. Its squared operator norm multiplies the bound.

**Theorem 1.7 (Persistence of the normalized converse).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.not_hs_sqrt_diff_of_add_traceClass_not_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.not_hs_sqrt_diff_of_add_traceClass_not_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a corrected positive covariance, the root difference between it and the uncorrected positive covariance is Hilbert–Schmidt in the same normalizing congruence. Subtraction reduces a hypothetical Hilbert–Schmidt difference to the uncorrected converse.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.isCompactOperator_sqrt_sub_of_isCompactOperator_sub`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.not_hs_sqrt_diff_of_add_traceClass_not_hs`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.powers_stormer_hsSq_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.powers_stormer_isHilbertSchmidt`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.powers_stormer_sharp`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.quarterPower_add_traceClass_congruence_sqrt_hs`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.quarterPower_add_traceClass_sqrt_hs`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound](NullDiamondConverseLowerBound.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt](QuarterPowerSqrtHilbertSchmidt.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Compact](../TraceClass/Compact.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/IdealNorm](../TraceClass/IdealNorm.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Spectral](../TraceClass/Spectral.md)
