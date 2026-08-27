# Finite Observability Equivalence

## Abstract

Finite readout residual, full rank, and Gram positivity are equivalent.

**Theorem 1.1 (Kernel, rank, and Gram criteria agree).**

$$\begin{aligned}\forall V, Y: \operatorname{Type},\\{}[\operatorname{NormedAddCommGroup}(V)], [\operatorname{InnerProductSpace}(\mathbb{R}, V)], [\operatorname{FiniteDimensional}(\mathbb{R}, V)],\\{}[\operatorname{NormedAddCommGroup}(Y)], [\operatorname{InnerProductSpace}(\mathbb{R}, Y)], [\operatorname{FiniteDimensional}(\mathbb{R}, Y)],\\\forall T: \operatorname{LinearMap}(\mathbb{R}, V, V), C: \operatorname{LinearMap}(\mathbb{R}, V, Y), n: \mathbb{N},\\{}let O_{n}: \operatorname{LinearMap}(\mathbb{R}, V, \operatorname{PiLp}(2, \operatorname{Fin}(n) \to Y)), O_{n}(x) = (C(T^{t} x))_{t: \operatorname{Fin}(n)};\\{}let N_{n} = \operatorname{ker}(O_{n}); let W_{n} = O_{n}^{*} O_{n};\\{}N_{n} = \{0\} \iff \operatorname{finrank}(\mathbb{R}, \operatorname{range}(O_{n})) = \operatorname{finrank}(\mathbb{R}, V) \iff \forall x: V, x \neq 0 \Rightarrow 0 < \langle x, W_{n} x \rangle_{\mathbb{R}}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/FiniteObservabilityEquivalence.finite_observability_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stacked readout is constructed from every iterate before the finite horizon. Its residual is its kernel and its Gram operator is the adjoint composed with the stacked readout. Rank-nullity and the Gram energy identity make all three public criteria equivalent.

## References

- Truth anchor: `D5/S3/Observer/Linear/FiniteObservabilityEquivalence.finite_observability_equivalence`
- Dependency: [D5/S3/Observer/Linear/DiscountedObservabilityGramianKernel](DiscountedObservabilityGramianKernel.md)
