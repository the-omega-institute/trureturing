# Result

## Abstract

Result of centered spherical matrix kernels.

**Theorem 1.1 (A family of counterexamples).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Result.family_refutes`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Result.family_refutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every dimension d at least three and for every beta strictly between zero and (d minus two) divided by d, the three-input kernel is continuous, symmetric, and invariant under all orthogonal transformations. Its averaged kernel is conditionally positive definite, but normalized surface measure does not minimize its energy. Surface measure has energy zero, while any Dirac probability measure has energy ((d minus one) divided by d) times (beta minus (d minus two) divided by d), which is negative.

**Theorem 1.2 (Failure of the characterization).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/bilyk-et-al-2022-averaged-kernel-characterization-refutation` (refuted) by `D5/S3/Analytic/MultivariateEnergy/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bilyk-et-al-2022-averaged-kernel-characterization-refutation","declaration_gid":"D5/S3/Analytic/MultivariateEnergy/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

The universal equivalence between minimization by normalized surface measure and conditional positive definiteness of the averaged kernel is false. The family at dimension three, arity three, and beta equal to one tenth satisfies the latter property and violates the former. Orthogonal invariance includes invariance under rotations.

## References

- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Result.family_refutes`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Result.result`
- Dependency: [D5/S3/Analytic/MultivariateEnergy/Energy](Energy.md)
