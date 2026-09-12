# Artin-Schreier Quadratic Root Uniqueness

## Abstract

Roots of one Artin-Schreier equation with equal constant coefficients coincide.

**Theorem 1.1 (Equal constant coefficients determine the root).**

$$\forall R, \operatorname{CommRing}\left(R\right) \land \operatorname{characteristic}\left(R\right) = 2 \Rightarrow \forall F, G, f \in \operatorname{PowerSeries}\left(R\right), ((F^{2} + F = f) \land ((G^{2} + G = f) \land (\operatorname{constantCoeff}\left(F\right) = \operatorname{constantCoeff}\left(G\right)))) \Rightarrow F = G$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ArtinSchreierQuadraticRootUniqueness.eq_of_square_add_eq_square_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a commutative ring of characteristic two and let F, G, and f be formal power series over R. If F squared plus F and G squared plus G both equal f, and F and G have the same constant coefficient, then F equals G. The right-hand side and both candidate roots remain arbitrary.

Set D=F+G. Characteristic two turns the two equations into D squared plus D=0, hence D times D+1 is zero. The constant coefficient of D is zero, so D+1 has constant coefficient one and is a unit in the power-series ring. Cancelling that factor gives D=0 and therefore F=G. This is a symbolic ring argument; it uses no finite search or numerical certificate.

## References

- Truth anchor: `D5/S3/Arith/ArtinSchreierQuadraticRootUniqueness.eq_of_square_add_eq_square_add`
