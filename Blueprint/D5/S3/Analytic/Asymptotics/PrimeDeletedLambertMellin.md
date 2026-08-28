# Prime-Deleted Lambert--Mellin Bridge

## Abstract

A prime-deleted Lambert heat kernel has the expected Mellin product.

**Theorem 1.1 (The deleted Lambert kernel has a zeta-product Mellin transform).**

$$\begin{aligned}\forall p: \mathbb{N}, r: \mathbb{N}, w: \mathbb{C};\\{}\operatorname{Prime}(p) \land 1 < r \land 1 < \Re(w) \Rightarrow\\{}\operatorname{mellin}(\operatorname{primeDeletedLambertKernel}(p, r), w) = \Gamma(w) \zeta(w) \zeta(w + r) (1 - p^{{-{w + r}}}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/PrimeDeletedLambertMellin.prime_deleted_lambert_mellin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p and an integer r greater than one, the public coefficient primeDeletedDivisorSum is the finite divisor-antidiagonal sum that retains d to the negative r power exactly when p does not divide d. The public heat kernel is the resulting exponential series over positive indices; its zero coefficient vanishes.

The displayed binders reproduce the Lean signature: p and r are natural numbers, p is prime, r is greater than one, w is complex, and the real part of w is greater than one. These assumptions imply the second absolute-convergence inequality for w plus r.

The proof identifies the explicit deletion predicate with the trivial Dirichlet character modulo p, rewrites the divisor coefficient as a Dirichlet convolution, and proves heat-series summability from a linear coefficient bound. Mathlib's generic Mellin theorem then supplies the Gamma integral and interchange, while the trivial character formula supplies the deleted Euler factor.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/PrimeDeletedLambertMellin.prime_deleted_lambert_mellin`
