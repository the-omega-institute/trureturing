# Discounted Observability Gramian Positivity

## Abstract

A convergent discounted observability Gramian is positive semidefinite.

**Theorem 1.1 (The discounted observability Gramian is positive semidefinite).**

$$\forall K, V, Y, T, C, \beta,\\{}\operatorname{RCLike}(K) \land \operatorname{FiniteDimensional}(K, V) \land \operatorname{FiniteDimensional}(K, Y) \land\\{}0 < \beta < 1 \land \sqrt{\beta} \left\lVert T \right\rVert < 1 \Rightarrow\\{}W_{\beta} = \sum_{n=0}^{\infty} \beta^{n} {T^{*}}^{n} C^{*} C T^{n} \land 0 \le W_{\beta}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/DiscountedObservabilityGramianPositivity.discounted_observability_gramian_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and Y be finite-dimensional inner-product spaces over a real or complex scalar field. The evolution T and readout C are arbitrary linear maps on these source carriers.

The Gramian is constructed as the norm-convergent infinite sum of the discounted adjoint Gram terms. Its public assumptions retain both the source discount range and the stated square-root norm bound.

Each summand is a nonnegative real scalar multiple of an adjoint composition. A geometric majorant proves summability, and continuous evaluation, inner product, and real-part maps carry the operator sum to a sum of nonnegative quadratic forms.

Repository searches found no existing discounted observability Gramian theorem. The proof directly applies the pinned library's adjoint-composition positivity, operator norm bounds, geometric summability, and infinite-sum transport lemmas.

## References

- Truth anchor: `D5/S3/Observer/Linear/DiscountedObservabilityGramianPositivity.discounted_observability_gramian_nonnegative`
