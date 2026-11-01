# Inverse-Gram Dual Pairing

## Abstract

Inverse-Gram dual vectors pair with the realizing rows by the Kronecker delta.

Given a realizing matrix M for the six-length Gram matrix G, form the dual vector D_i from row i of G inverse and the rows of M. The Lorentz pairing of D_i with the j-th realizing row is then exactly the Kronecker delta. The negative determinant assumption supplies the nonsingularity needed for the inverse.

**Theorem 1.1 (Dual vectors recover the realizing row coordinates).**

$$\forall l \in Length6,\; \forall M \in Mat4,\; \left(\forall i \in Fin4,\; \forall j \in Fin4,\; \operatorname{lorentz}\left(\operatorname{row}\left(M, i\right), \operatorname{row}\left(M, j\right)\right) = \operatorname{entry}\left(\operatorname{lengthGram}\left(l\right), i, j\right)\right) \Rightarrow \left(\operatorname{det}\left(\operatorname{lengthGram}\left(l\right)\right) < 0 \Rightarrow \left(\forall i \in Fin4,\; \forall j \in Fin4,\; \operatorname{lorentz}\left(\operatorname{dualVector}\left(\operatorname{lengthGram}\left(l\right), M, i\right), \operatorname{row}\left(M, j\right)\right) = \operatorname{delta}\left(i, j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramDualPairing.dual_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof expands the Lorentz bilinear form and rearranges the finite sums into the matrix product G inverse times G. Nonsingular inverse cancellation reduces that product to the identity matrix entry.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramDualPairing.dual_pairing`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramBody](LengthGramBody.md)
