# Quarter-power Hilbert–Schmidt bounds for positive square roots

## Abstract

Sharp quarter-power square-root estimates, bounded congruence, and compact coercivity.

Stage 3A of issue #34535. The operator estimate supplies the square-root trace step for Eq. (71) of Satishchandran and Sorce when the covariance operators admit the required quarter-power factorization.

**Definition 1.1 (Quarter root).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterRoot`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The quarter root of an operator is the continuous-functional-calculus square root of its square root.

**Definition 1.2 (Rectangular adjoint congruence).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.adjointCongr`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.adjointCongr` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For C from K to H and an endomorphism A of H, congruence is the endomorphism C* A C of K.

**Definition 1.3 (Squared Hilbert–Schmidt norm).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.hsSq`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.hsSq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Given a proof that W is Hilbert–Schmidt, sum the squared norms of its columns in a chosen Hilbert basis. Parseval identifies the sum in every Hilbert basis.

**Theorem 1.4 (Factor through a bounded endomorphism).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.exists_bounded_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.exists_bounded_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

If L maps K into H, D acts on K, c is nonnegative and ‖Lx‖ ≤ c ‖Dx‖ for every x, then L = ZD for a bounded map Z from K into H with ‖Z‖ ≤ c. Extend from the range of D to its closure and compose with orthogonal projection.

**Theorem 1.5 (Rectangular Hilbert–Schmidt estimate).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.adjointCongr_hsSq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.adjointCongr_hsSq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Congruence of a Hilbert–Schmidt W by a bounded map Z is Hilbert–Schmidt. Its squared norm is at most ‖Z‖⁴ times that of W. Rectangular Parseval transfers the column sum to the adjoint.

**Theorem 1.6 (Quarter-power factorization under congruence).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_congruence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For positive A and B with B − A = A^(1/4) W A^(1/4) and W Hilbert–Schmidt, set M = C* A C. There is Z with ‖Z‖² ≤ ‖C‖ and A^(1/4) C = Z M^(1/4). The congruence of B − A equals M^(1/4) (Z* W Z) M^(1/4), and Z* W Z is Hilbert–Schmidt with squared norm at most ‖C‖² times that of W.

**Theorem 1.7 (Finite-dimensional sharp estimate).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.finite_quarterPower_sqrt_hsSq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.finite_quarterPower_sqrt_hsSq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

If A and B are positive, W is Hilbert–Schmidt and B − A = A^(1/4) W A^(1/4), the squared Hilbert–Schmidt norm of √B − √A is at most that of W. For invertible A, express both squared Hilbert–Schmidt norms as traces and use cyclicity. In an eigenbasis of √B, Cauchy–Schwarz gives k ≥ 1/p for the inverse-quarter-root column square k, where p is the quarter-root column square. For each eigenvalue r the remainder is bounded below by r(r − p)²(r + 2p)/p². Scalar regularization and polynomial approximation cover singular A.

**Theorem 1.8 (Equality on the scalar Hilbert space).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For A = 1, B = 0, and W = −1 on ℂ, the quarter-power factorization holds and both squared Hilbert–Schmidt norms are one.

**Theorem 1.9 (Sharp estimate on arbitrary Hilbert spaces).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_hsSq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_hsSq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For positive A and B with B − A = A^(1/4) W A^(1/4) and W Hilbert–Schmidt, √B − √A is Hilbert–Schmidt with squared norm at most that of W. Compress over finite subsets of a Hilbert basis, zero-extend the square roots and pass the uniform bound on each finite column sum to the strong limit.

**Theorem 1.10 (Norm bounds).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_hsNorm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_hsNorm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Under the quarter-power factorization, the Hilbert–Schmidt norm of √B − √A is at most that of W and hence at most √2 times that of W.

**Theorem 1.11 (Trace class of the squared root difference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_sq_isTraceClass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_sq_isTraceClass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Under the quarter-power factorization, the square of √B − √A is trace class by the product theorem for two Hilbert–Schmidt operators.

**Theorem 1.12 (Sharp estimate after congruence).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_congruence_sqrt_hsSq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_congruence_sqrt_hsSq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The difference between the square roots of C* B C and C* A C is Hilbert–Schmidt, with squared norm at most ‖C‖² times that of W under the quarter-power factorization.

**Theorem 1.13 (Compact coercivity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.compact_add_one_coercive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.compact_add_one_coercive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

If T is compact and T and J are self-adjoint, ker J = {0}, and 1 + T ± J are positive, then N = 1 + T has trivial kernel and satisfies c I ≤ N for some c > 0. Use the signed quadratic forms to rule out a −1 eigenvector of T, then apply the compact lower bound.

**Theorem 1.14 (Hilbert–Schmidt coercivity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.hilbertSchmidt_add_one_coercive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.hilbertSchmidt_add_one_coercive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The compact coercivity conclusion holds under the same self-adjointness, signed positivity, and kernel hypotheses when T is Hilbert–Schmidt.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.adjointCongr`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.adjointCongr_hsSq_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.compact_add_one_coercive`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.exists_bounded_factor`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.finite_quarterPower_sqrt_hsSq_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.hilbertSchmidt_add_one_coercive`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.hsSq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_congruence`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_congruence_sqrt_hsSq_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_hsNorm_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_hsSq_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_sharp`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterPower_sqrt_sq_isTraceClass`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.quarterRoot`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/FiniteCompression](../TraceClass/FiniteCompression.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/GeneralProduct](../TraceClass/GeneralProduct.md)
