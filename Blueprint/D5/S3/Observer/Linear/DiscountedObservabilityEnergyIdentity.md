# Discounted Observability Energy Identity

## Abstract

The discounted observability Gramian quadratic form equals total discounted readout energy.

**Theorem 1.1 (The Gramian quadratic form is total discounted readout energy).**

$$\forall K, V, Y,\\{}\operatorname{RCLike}(K) \land \operatorname{NormedAddCommGroup}(V) \land \operatorname{InnerProductSpace}(K, V) \land \operatorname{FiniteDimensional}(K, V) \land\\{}\operatorname{NormedAddCommGroup}(Y) \land \operatorname{InnerProductSpace}(K, Y) \land \operatorname{FiniteDimensional}(K, Y) \land\\{}T: \operatorname{LinearMap}(K, V, V), C: \operatorname{LinearMap}(K, V, Y), \beta\in \mathbb{R}, x\in V,\\{}0 < \beta \land \sqrt{\beta} \left\lVert T \right\rVert < 1 \Rightarrow\\{}\Re(\langle x, \operatorname{discountedObservabilityGramian}(T, C, \beta)(x) \rangle) = \sum_{n=0}^{\infty} \beta^{n} \left\lVert \operatorname{observedIterate}(T, C, n, x) \right\rVert^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/DiscountedObservabilityEnergyIdentity.discounted_observability_energy_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and Y be finite-dimensional inner-product spaces over a real or complex scalar field. Construct the discounted observability Gramian from the evolution T and readout C using the canonical norm-convergent operator series.

For positive beta under the stated square-root norm bound, the real part of its quadratic form at x is the infinite sum of beta to the nth power times the squared norm of the nth observed iterate.

Continuous evaluation, inner product, and real-part maps transport the summable operator series term by term. The pinned library's adjoint-composition identity identifies each transported term with its squared readout norm.

Repository and pinned-library searches found no public packaged theorem for the complete identity. Existing canonical Gramian and iterate constructions are reused directly.

## References

- Truth anchor: `D5/S3/Observer/Linear/DiscountedObservabilityEnergyIdentity.discounted_observability_energy_identity`
- Dependency: [D5/S3/Observer/Linear/DiscountedObservabilityGramianPositivity](DiscountedObservabilityGramianPositivity.md)
