# Adjoint-Kernel Redundancy

## Abstract

The adjoint kernel is exactly the space of redundant protocol coefficients.

**Theorem 1.1 (Adjoint-kernel coefficients are exactly vanishing protocol combinations).**

$$\begin{aligned}\forall V, iota: \operatorname{Type},\\{}[\operatorname{NormedAddCommGroup}(V)], [\operatorname{InnerProductSpace}(\mathbb{R}, V)],\\{}[\operatorname{FiniteDimensional}(\mathbb{R}, V)], [\operatorname{Fintype}(iota)],\\{}\forall ell: iota \to V, a: \operatorname{EuclideanSpace}(\mathbb{R}, iota),\\{}let M: \operatorname{LinearMap}(\mathbb{R}, V, \operatorname{EuclideanSpace}(\mathbb{R}, iota)) = \operatorname{comp}(\operatorname{toLinearMap}(\operatorname{symm}(\operatorname{withLpLinearEquiv}(2, \mathbb{R}, iota \to \mathbb{R}))), \operatorname{linearPi}((i: iota \mapsto \operatorname{innerSL}(\mathbb{R}, ell\left(i\right)))));\\a \in \operatorname{ker}(\operatorname{adjoint}(M)) \Leftrightarrow \operatorname{finSum}((i: iota \mapsto \operatorname{smul}(a\left(i\right), ell\left(i\right)))) = 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/AdjointKernelRedundancy.adjoint_kernel_redundancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite family ell consist of protocol representatives in a finite-dimensional real Hilbert state space. The analysis map M records the inner product with every representative.

For every Euclidean coefficient vector a, the adjoint M-star applied to a is the finite synthesis sum of a_i times ell_i. Consequently a lies in the adjoint kernel exactly when that linear combination vanishes.

Thus a protocol-side residual direction need not mean the absence of a state. It records an exact linear dependence among the selected protocol representatives.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/AdjointKernelRedundancy.adjoint_kernel_redundancy`
