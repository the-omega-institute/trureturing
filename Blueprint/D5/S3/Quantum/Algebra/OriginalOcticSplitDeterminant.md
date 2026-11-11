# The labeled octic window

## Abstract

The split determinant of the original octic window is irreducible over every characteristic-zero splitting field.

Let alpha be an element of a field D with alpha to the eighth power equal to two. Let sigma_0 through sigma_7 be embeddings into a characteristic-zero field k. Fix a primitive eighth root zeta in k and preserve the labels sigma_i(alpha)=sigma_0(alpha) zeta^i. The four columns are the images of 1, alpha, alpha^3 and alpha^4 in that order. The polynomial is the determinant of the eight columns [B | diag(q) B], with rows labeled zero through seven. In the formulas, fourSets is the set of all four-element subsets of Fin 8, and RingHomFamily(Fin 8,D,k) means a family of eight unital ring homomorphisms from D to k. The exponent i is the representative zero through seven of its original label.

**Lemma 1.1 (The exact normalized coefficient count).**

$$\operatorname{card}(\{I\in fourSets\mid\operatorname{integerCoefficient}(I)=0\})=18$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.coefficient_zero_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are seventy four-element label sets. The normalized integer coefficient function vanishes at eighteen of them. Its other values belong to the set consisting of plus or minus one, two and four.

**Theorem 1.2 (Structure of the actual determinant).**

$$\forall k, \operatorname{Field}(k)\land\operatorname{CharZero}(k)\implies\forall a: k, \forall z: k, a^{8}=2\land\operatorname{IsPrimitiveRoot}(z, 8)\implies\operatorname{IsHomogeneous}(\operatorname{splitDeterminant}(\operatorname{originalWindowMatrix}(a, z)), 4)\land(\forall i: \operatorname{Fin}(8), \operatorname{degreeOf}(i, \operatorname{splitDeterminant}(\operatorname{originalWindowMatrix}(a, z)))\le1)\land\operatorname{card}(\{I\in fourSets\mid\operatorname{coeff}(\operatorname{splitDeterminant}(\operatorname{originalWindowMatrix}(a, z)), \operatorname{squareExponent}(I))=0\})=18$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement derives homogeneity of degree four, degree at most one in each variable and exactly eighteen zero squarefree quartic coefficients from the root relations themselves.

Put s=zeta+zeta^3, so s squared equals minus two. If U is the matrix of the first four rows of B, the last four rows are R U, where the rows of R are (-1,-s,2,s), (-s,1,s,0), (0,-s,1,s) and (-s,2,s,-1). The square of det(U) is 128. Block elimination expresses the eight-by-eight determinant as 128 times the determinant whose entry (i,j) is R(i,j)(q_(4+i)-q_j). Expanding this four-by-four determinant gives precisely the normalized integer coefficients counted above. No row permutation changes the original labels.

**Theorem 1.3 (Irreducibility with the original embeddings).**

$$\forall k, \forall D, \operatorname{Field}(k)\land\operatorname{CharZero}(k)\land\operatorname{Field}(D)\implies\forall alpha: D, \forall sigma: \operatorname{RingHomFamily}(\operatorname{Fin}(8), D, k), \forall z: k, alpha^{8}=2\land\operatorname{IsPrimitiveRoot}(z, 8)\land(\forall i: \operatorname{Fin}(8), \operatorname{sigma}(i, alpha)=\operatorname{sigma}(0, alpha)\cdot z^{i})\implies\operatorname{Irreducible}(\operatorname{splitDeterminant}(\operatorname{originalFieldWindowMatrix}(alpha, sigma)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying each embedding to alpha^8=2 identifies its row with the root matrix used in the structure theorem. The homogeneous multiaffine quartic obstruction applies because eighteen is less than twenty. Thus the actual determinant is irreducible over k. The statement quantifies every characteristic-zero field containing these embeddings and the primitive root, so it also applies after further field extension.

The original field element, its four powers and all eight embedding labels remain explicit. This determinant statement does not assert a classification of rational windows with equal quotient support.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.coefficient_zero_count`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_structure`
- Dependency: [D5/S3/Quantum/Algebra/SplitQuarticIrreducibility](SplitQuarticIrreducibility.md)
