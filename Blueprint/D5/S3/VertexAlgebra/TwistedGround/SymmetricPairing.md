# A Symmetric Pairing on the Selected Actual Ground

## Abstract

A Symmetric Pairing on the Selected Actual Ground

**Theorem 1.1 (A Symmetric Pairing on the Selected Actual Ground).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/SymmetricPairing.actual_symmetric_ground_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/SymmetricPairing.actual_symmetric_ground_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integral symmetric even lattice D with integer unit determinant hu, the exact selected ActualGround(D,hu) admits a nondegenerate symmetric complex bilinear form. The form is invariant under the original reflection quotient. For every integral charge alpha it satisfies B(R_alpha u,v)=(-1)^(G(alpha,alpha)/2) B(u,R_alpha v), with the same charge on both sides.

Let A be the finite average on bilinear forms and F interchange arguments. The operator S=A+F composed with A has trace two, since tr(A)=tr(F composed with A)=one. Hence S is nonzero. An elementary bilinear basis contains a seed with nonzero image. This image is symmetric by the formula B(u,v)=A(seed)(u,v)+A(seed)(v,u), and it is invariant because each summand is invariant.

The invariant nonzero form has zero radical by irreducibility of the selected representation. Finite-dimensional duality makes it nondegenerate. The original charge square law and invariance imply the signed adjointness law. The construction uses the original selected carrier and representation, including rank zero.

The finite ground pairing does not by itself construct an oscillator Wick extension, an all-source opposite covariance theorem, a two-twisted-input intertwiner, a Monster action, a fusion rule, string theory or an AdS/CFT bridge.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/SymmetricPairing.actual_symmetric_ground_pairing`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FlipAverage](FlipAverage.md)
