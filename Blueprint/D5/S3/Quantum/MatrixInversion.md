# Affine Matrix Inversion

## Abstract

Weighted matrix inverses factor through an affine segment in noncommutative order.

**Lemma 1.1 (Weighted inverses factor through the affine segment).**

$$\forall \rho,\sigma \in M_{n}(\mathbb{C}),\ \forall a,b,u \in \mathbb{R},\ \rho>0 \land \sigma>0 \land a>0 \land b>0 \land 0\leq u\leq1 \Rightarrow (a\cdot\rho^{-1}+b\cdot\sigma^{-1}=\rho^{-1}\cdot(a\cdot\sigma+b\cdot\rho)\cdot\sigma^{-1}) \land ((1-u)\cdot\rho^{-1}+u\cdot\sigma^{-1})^{-1}=\sigma\cdot((1-u)\cdot\sigma+u\cdot\rho)^{-1}\cdot\rho$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MatrixInversion.positive_definite_inversion_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive-definite finite square complex matrices rho and sigma, positive real numbers a and b, and u in the closed unit interval, the weighted inverse sum factors through the affine segment. The inverse of the corresponding weighted sum is sigma times the inverse segment times rho, in that order. No commutativity of rho and sigma is assumed. The formal module also exposes the factorization and affine inverse identity as independent interfaces.

## References

- Truth anchor: `D5/S3/Quantum/MatrixInversion.positive_definite_inversion_identity`
