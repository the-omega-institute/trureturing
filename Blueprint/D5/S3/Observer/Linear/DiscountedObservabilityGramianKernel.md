# Discounted Observability Gramian Kernel

## Abstract

The discounted observability Gramian kernel is the all-future readout kernel.

**Theorem 1.1 (The Gramian kernel is the all-future readout kernel).**

$$\forall K, V, Y: \operatorname{Type}, [\operatorname{RCLike}(K)], [\operatorname{NormedAddCommGroup}(V)], [\operatorname{InnerProductSpace}(K, V)], [\operatorname{FiniteDimensional}(K, V)], [\operatorname{NormedAddCommGroup}(Y)], [\operatorname{InnerProductSpace}(K, Y)], [\operatorname{FiniteDimensional}(K, Y)]\\{}T: \operatorname{LinearMap}(K, V, V), C: \operatorname{LinearMap}(K, V, Y), \beta: \mathbb{R},\\{}N_{\infty} = \operatorname{iInf}(n, \operatorname{ker}(C \circ T^{n})),\\{}\\{}0 < \beta < 1 \land \sqrt{\beta} \left\lVert T \right\rVert < 1 \Rightarrow\\{}W_{\beta} = \sum_{n=0}^{\infty} \beta^{n} {T^{*}}^{n} C^{*} C T^{n} \land \operatorname{ker}(W_{\beta}) = N_{\infty}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/DiscountedObservabilityGramianKernel.discounted_observability_gramian_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and Y be finite-dimensional inner-product spaces over a real or complex scalar field. The evolution T and readout C are arbitrary linear maps, and beta satisfies the stated discount and norm convergence restrictions.

The Gramian is the norm-convergent sum of the discounted adjoint Gram terms constructed in the positivity result. The right side is the canonical all-future readout kernel imported from the observer memory family.

Each quadratic-form summand is beta to the nth power times the squared norm of the nth observed iterate. Since every term is nonnegative and beta is positive, zero total energy is equivalent to every future readout vanishing.

Repository searches found no packaged Gramian-kernel theorem. The proof applies the pinned library's adjoint norm identity, transport of summable series through continuous maps, and strict positivity of a nonnegative series containing a positive term.

## References

- Truth anchor: `D5/S3/Observer/Linear/DiscountedObservabilityGramianKernel.discounted_observability_gramian_kernel`
- Dependency: [D5/S3/Observer/Linear/DiscountedObservabilityGramianPositivity](DiscountedObservabilityGramianPositivity.md)
- Dependency: [D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace](../../ObserverMemory/Dynamics/MaximalUnobservableSubspace.md)
