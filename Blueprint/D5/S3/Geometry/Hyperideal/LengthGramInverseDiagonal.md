# Positive Diagonal of the Inverse Length Gram Matrix

## Abstract

The inverse of a six-length Lorentz Gram matrix has positive diagonal entries.

For six positive lengths, the four by four length Gram matrix has a negative determinant in the hyperideal regime. Each diagonal cofactor is a three by three Gram determinant with all three hyperbolic cosine entries greater than one, hence negative. Dividing the negative cofactors by the negative determinant gives strict positivity on the diagonal of the inverse.

**Theorem 1.1 (Strict positivity of every inverse diagonal entry).**

$$\forall l \in Length6,\; \left(\forall k \in Fin6,\; \operatorname{l}\left(k\right) > 0\right) \Rightarrow \left(\operatorname{det}\left(\operatorname{lengthGram}\left(l\right)\right) < 0 \Rightarrow \left(\forall i \in Fin4,\; \operatorname{entry}\left(\operatorname{inv}\left(\operatorname{lengthGram}\left(l\right)\right), i, i\right) > 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramInverseDiagonal.inverse_diagonal_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof expands the four principal adjugate minors using the finite three by three determinant formula. The elementary inequality 1-u squared-v squared-w squared-2uvw < 0 for u,v,w greater than one supplies their signs. Matrix.inv_def then combines a negative determinant with a negative adjugate entry.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramInverseDiagonal.inverse_diagonal_pos`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramBody](LengthGramBody.md)
