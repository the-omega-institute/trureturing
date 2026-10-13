# GenericLieLengthGenericity

## Abstract

A nonzero polynomial determinant transfers one full-span tuple to almost every tuple.

**Theorem 1.1 (ae_mvPolynomial_ne_zero).**

$$\forall (n : \mathbb{N}) (p : \operatorname{MvPolynomial} (\operatorname{Fin} n) \mathbb{R}) , p \neq 0 \to \forall^{m} (x : \operatorname{Fin} n \to \mathbb{R}) , \operatorname{MvPolynomial} . \operatorname{eval} x p \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthGenericity.ae_mvPolynomial_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero real multivariate polynomial vanishes only on a Lebesgue null set. The proof inducts on the number of variables and uses the finite univariate root set and the product-measure theorem.

**Theorem 1.2 (ae_span_top_of_witness).**

$$\forall (M : \operatorname{Type} *) [ \operatorname{LieRing} M ] [ \operatorname{LieAlgebra} \mathbb{R} M ] [ \operatorname{FiniteDimensional} \mathbb{R} M ] (g d L : \mathbb{N}) (b : \operatorname{Module} . \operatorname{Basis} (\operatorname{Fin} d) \mathbb{R} M) (S0 : \operatorname{Fin} g \to M) , \operatorname{rightSpan} (K := \mathbb{R}) S0 L = \operatorname{Top}.\operatorname{top} \to \forall^{m} (x : \operatorname{Fin} g \to \operatorname{Fin} d \to \mathbb{R}) , \operatorname{rightSpan} (K := \mathbb{R}) (\operatorname{fun} (i : \operatorname{Fin} g) \mapsto b . \operatorname{equivFun} . \operatorname{symm} (x i)) L = \operatorname{Top}.\operatorname{top}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthGenericity.ae_span_top_of_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One spanning tuple supplies coefficients for a determinant polynomial which evaluates to one. Its nonzero evaluations give full span for almost all tuples of real basis coordinates.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthGenericity.ae_mvPolynomial_ne_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthGenericity.ae_span_top_of_witness`
- Dependency: [D5/S3/Quantum/Algebra/GenericLieLengthFiltration](GenericLieLengthFiltration.md)
