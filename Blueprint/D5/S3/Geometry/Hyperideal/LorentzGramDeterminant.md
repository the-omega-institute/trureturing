# The determinant of a Lorentz Gram matrix

## Abstract

Lorentz Gram determinants are negative squares of realizing determinants.

A four by four real matrix M has row vectors in the standard space-positive, time-negative Lorentz form. If G is their pairwise Gram matrix, then G=M J M^T for J=diag(1,1,1,-1). The determinant therefore records the orientation-free volume square with the single Lorentz sign.

**Theorem 1.1 (Exact Lorentz Gram determinant identity).**

$$\forall M \in Mat4,\; \forall G \in Mat4,\; \left(\forall i \in Fin4,\; \forall j \in Fin4,\; \operatorname{lorentz}\left(\operatorname{row}\left(M, i\right), \operatorname{row}\left(M, j\right)\right) = \operatorname{entry}\left(G, i, j\right)\right) \Rightarrow \operatorname{det}\left(G\right) = -\operatorname{det}\left(M\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LorentzGramDeterminant.lorentz_gram_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof first identifies the Gram matrix with the explicit matrix product M*J*M-transpose by expanding the finite Lorentz sum. Multiplicativity of determinant, transpose invariance, and the four diagonal entries of J then give det(G)=-(det(M))^2.

**Theorem 1.2 (The six-length Gram specialization).**

$$\forall l \in Length6,\; \forall M \in Mat4,\; \left(\forall i \in Fin4,\; \forall j \in Fin4,\; \operatorname{lorentz}\left(\operatorname{row}\left(M, i\right), \operatorname{row}\left(M, j\right)\right) = \operatorname{lengthGram}\left(l, i, j\right)\right) \Rightarrow \operatorname{det}\left(\operatorname{lengthGram}\left(l\right)\right) = -\operatorname{det}\left(M\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LorentzGramDeterminant.length_gram_determinant_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the general identity to the existing LengthGramBody lengthGram matrix gives the determinant factorization for every supplied Lorentz realization of the same six-length Gram data.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LorentzGramDeterminant.length_gram_determinant_factorization`
- Truth anchor: `D5/S3/Geometry/Hyperideal/LorentzGramDeterminant.lorentz_gram_determinant`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramBody](LengthGramBody.md)
