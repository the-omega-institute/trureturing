# Quotient-Compatible Residual Transport

## Abstract

Isometric quotient transport preserves canonical residual norms and costs.

**Theorem 1.1 (Quotient transport preserves residual cost).**

$$\begin{gathered}M_{k} \subset H_{k}, M_{j} \subset H_{j}, T_{kj}: H_{k} \to H_{j},\\{}T_{kj}(M_{k}) \subset M_{j}, T_{kj}(x_{k}) - x_{j} \in M_{j},\\{}\overline{T_{kj}}([x_{k}]) = [x_{j}] \land\\{}(\operatorname{Isometry}\left(\overline{T_{kj}}\right) \Rightarrow\\{}\Vert x_{k}-P_{M_{k}}(x_{k}) \Vert = \Vert x_{j}-P_{M_{j}}(x_{j}) \Vert \land\\{}\frac{1}{2} \Vert x_{k}-P_{M_{k}}(x_{k}) \Vert^{{2}} = \frac{1}{2} \Vert x_{j}-P_{M_{j}}(x_{j}) \Vert^{{2}}) \land\\{}\exists f, g: \operatorname{ContinuousLinearMap}\left(\mathbb{R}, \mathbb{R}\right), z\in\mathbb{R},\\{}(\forall x, f(x) = 0 \Leftrightarrow g(x) = 0) \land\\{}\frac{1}{2} \Vert f(z) \Vert^{{2}} \neq \frac{1}{2} \Vert g(z) \Vert^{{2}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/QuotientResidualTransport.quotient_residual_transport_and_zero_set_countermodel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the two charts be real-or-complex inner-product spaces with closed subspaces admitting orthogonal projections. A continuous linear transition preserves the subspaces and carries the two selected points to the same target quotient class.

The quotient transition is constructed canonically with the quotient lift. When it is an isometry, the imported canonical quotient-to-orthogonal-complement equivalence identifies quotient norms with the norms of the two projection residuals. Their half-squared costs therefore agree.

The final conjunct gives two explicit continuous linear residual maps on the real line. They have exactly the same zero set, but their costs at the displayed point differ, so zero-set agreement alone cannot supply cost invariance.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/QuotientResidualTransport.quotient_residual_transport_and_zero_set_countermodel`
- Dependency: [D5/S3/Quantum/Algebra/QuotientOrthogonalComplement](../Algebra/QuotientOrthogonalComplement.md)
