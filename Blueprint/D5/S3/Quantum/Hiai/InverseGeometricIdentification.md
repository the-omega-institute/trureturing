# InverseGeometricIdentification

## Abstract

Weighted symmetry and inversion of the spectral geometric mean.

**Theorem 1.1 (Unitary equivariance of real powers).**

$$\forall v: \operatorname{Level}(),\ \forall A: \operatorname{Type}(v),\ [\operatorname{CStarAlgebra}(A)], [\operatorname{PartialOrder}(A)], [\operatorname{StarOrderedRing}(A)],\ \forall U: \operatorname{unitary}(A),\ \forall a: A,\ \forall t: \mathbb{R},\ \operatorname{IsStrictlyPositive}(a)\implies\ \operatorname{rpow}(Ua\operatorname{star}(U), t)=U\operatorname{rpow}(a, t)\operatorname{star}(U)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/InverseGeometricIdentification.unitary_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every ordered complex C-star algebra, conjugation by a unitary intertwines every real spectral power of a strictly positive element. The conjugation is a star algebra automorphism; the continuous functional calculus is applied only to that automorphism. An arbitrary invertible congruence does not have this property.

**Theorem 1.2 (Weighted symmetry and inverse sandwich).**

$$\forall v: \operatorname{Level}(),\ \forall d: \operatorname{Type}(v),\ [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ \forall X, Y: \operatorname{Matrix}(d, d, \mathbb{C}),\ \forall t: \mathbb{R},\ \operatorname{PosDef}(X)\land \operatorname{PosDef}(Y)\implies\ \operatorname{geometricMean}(t, X, Y)=\operatorname{geometricMean}(1-t, Y, X)\land \operatorname{geometricMean}(-t, X, Y)=X\operatorname{inverse}(\operatorname{geometricMean}(t, X, Y))X$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/InverseGeometricIdentification.geometricMean_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For arbitrary finite complex square matrices X and Y that are positive definite, define G(t,X,Y) by the existing geometricMean: X to exponent one half, then the t-th spectral power of X to exponent minus one half times Y times X to exponent minus one half, then X to exponent one half. The base is the first matrix argument. For every real t, G(t,X,Y)=G(1-t,Y,X) and G(-t,X,Y)=X inverse(G(t,X,Y)) X.

Put C=X to exponent minus one half times Y times X to exponent minus one half. The unitary U=Y to exponent minus one half times X to exponent one half times C to exponent one half identifies the reversed normalization with U inverse(C) U adjoint. Unitary equivariance then turns its exponent 1-t into the conjugate of C to exponent t-1. Restoring the outer square roots combines powers of the same C to recover G(t,X,Y). No X/Y commutation is assumed.

The inverse sandwich follows from inversion of the square-root congruence and inverse(C to exponent t)=C to exponent minus t. At t=0 this uses the unit spectral power, so the endpoint is included. Empty matrix dimension is also included. Matrix nonsingular inverse agrees with Ring.inverse by Matrix.nonsing_inv_eq_ringInverse.

Substitution t=-theta gives G(1+theta,Y,X)=G(-theta,X,Y), including theta=0 and theta=1. These are classical geometric-mean identities. In Hiai Problem 5.18 they connect the inverse-mean variational formula to the positive-weight mean-trace concavity. Joint convexity assembly and the common-epsilon support-preserving positive semidefinite extension are additional mathematical obligations.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/InverseGeometricIdentification.geometricMean_identification`
- Truth anchor: `D5/S3/Quantum/Hiai/InverseGeometricIdentification.unitary_rpow`
- Dependency: [D5/S3/Quantum/Hiai/PsiMeanTraceConcavity](PsiMeanTraceConcavity.md)
