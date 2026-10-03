# Primary Associates in the Eisenstein Order

## Abstract

An Eisenstein integer whose norm is one modulo three has a primary associate.

**Theorem 1.1 (A norm-one unit makes the associate primary).**

$$\forall z \in E, \operatorname{N}\left(z\right) \equiv 1 (\mathrm{mod} 3) \Rightarrow \exists u \in E, \operatorname{IsUnit}\left(u\right) \land \operatorname{N}\left(u\right) = 1 \land uz \equiv 1 (\mathrm{mod} 3E).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/EisensteinPrimaryAssociate.exists_primary_associate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be the integer quadratic algebra with omega squared plus omega plus one equal to zero. If the norm of z is one modulo three, there is a unit u of norm one such that 3 divides uz - 1. A norm-one element is a unit because its conjugate is an inverse.

Modulo three, the norm-one coordinate pairs are (1,0), (2,0), (0,1), (0,2), (1,1), and (2,2). Each is the residue of an Eisenstein unit, and multiplication by its inverse gives the primary associate. This supplies unit normalization after a prime generator is obtained; it does not construct that generator or factor the golden block.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/EisensteinPrimaryAssociate.exists_primary_associate`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/EisensteinOddQuotient](EisensteinOddQuotient.md)
