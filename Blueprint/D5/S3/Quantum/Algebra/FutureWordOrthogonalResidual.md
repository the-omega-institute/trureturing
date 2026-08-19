# Future Words and Orthogonal Residuals

## Abstract

Finite expectation words characterize residuals and visible projections.

**Theorem 1.1 (Finite-word equality is orthogonal-residual equivalence).**

$$\forall k, E, S: \operatorname{Type},\ [\operatorname{RCLike}(k)],\ [\operatorname{NormedAddCommGroup}(E)],\ [\operatorname{InnerProductSpace}_{k}(E)],\ [\operatorname{FiniteDimensional}_{k}(E)],\ m \in \mathbb{N},\ e: \operatorname{Fin}(m + 1) \to E,\ X: S \to E,\ \rho, \sigma \in S,\ ((W_{m}^{e,X}(\rho) = W_{m}^{e,X}(\sigma)) \Leftrightarrow (X(\rho) - X(\sigma) \in \operatorname{span}_{k}(\operatorname{range}(e))^{\perp})) \land ((X(\rho) - X(\sigma) \in \operatorname{span}_{k}(\operatorname{range}(e))^{\perp}) \Leftrightarrow (P_{\operatorname{span}_{k}(\operatorname{range}(e))}(X(\rho)) = P_{\operatorname{span}_{k}(\operatorname{range}(e))}(X(\sigma)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FutureWordOrthogonalResidual.future_word_orthogonal_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite family of effects generate the visible subspace. The expectation word of a represented state records its inner product with each effect. Equality of two such words is equivalent to the difference of the represented states lying in the orthogonal complement of the visible span.

The same residual condition is equivalent to equality of the two canonical orthogonal projections onto the visible span. Both equivalences appear as explicit conjuncts in the named theorem.

Repository search found the existing complementary-projection machinery but no theorem with this complete finite-word characterization. Loogle returned exact single hits for the span-induction, orthogonality, and zero-projection declarations applied by the proof. The attempted shaped LeanSearch API query returned HTTP 404.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/FutureWordOrthogonalResidual.future_word_orthogonal_residual`
