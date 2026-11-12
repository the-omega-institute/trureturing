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

## Application to the Auric 41.13 window

For the Auric specialization, take the designated positive real root alpha = 2^(1/8), let D = Q(alpha), choose the designated primitive eighth root zeta, and put K = D(zeta). Fix a map lambda from K into an algebraically closed characteristic-zero field k. Let X be the Q-span of 1, alpha, alpha^3 and alpha^4. The actual quotient set QX consists of u/v with u and v in X and v nonzero; it contains 0 by taking u = 0 and v = 1, while every denominator used below is the nonzero v. The original labels are ordered 0 through 7, with Fin 8 and ZMod 8 carrying the same eight labels.

Let B be the exact eight-by-four matrix whose i-th row is the four transported values of 1, alpha, alpha^3 and alpha^4, and let P(q) be the determinant of [B | diag(q) B] with those original row labels. The forward inclusion is the actual-kernel calculation: for rational coordinates a,b with the denominator element of X nonzero, the vector (-a,b) is a nonzero kernel vector of the evaluated split matrix at q = embed(u/v). Therefore P vanishes on every actual quotient point, including the separately recorded zero point.

The reverse direction first transfers rational parameters to arbitrary coefficients in k. Clearing the finitely many linear denominators gives a polynomial identity in two blocks of coefficient variables; the rational coefficient points are Zariski dense because k has characteristic zero. Hence vanishing for every rational numerator and every nonzero rational denominator transfers to every k-valued numerator and denominator for which all eight transported denominators are nonzero.

On the open chart where the determinant vanishes and the cofactor product is nonzero, take the seventh adjugate column of the evaluated eight-by-eight matrix. Its first four entries with a minus sign define U and its last four entries define V; set H(q) = product over i of (B times V(q))_i. The identity M times adjugate(M) = det(M) times the identity gives q_i = (B times U(q))_i / (B times V(q))_i whenever H(q) is nonzero. This is the inverse chart used by the rational-parameter transfer.

The chart is nonempty at the square point qstar_i = sigma_i(alpha)^2. The determinant is zero because columns 2 and 5 coincide there. The cofactor in column 7, row 5 is the signed determinant of a seven-by-seven minor; after deleting the repeated column it is a permutation of a Vandermonde matrix on the seven remaining transported roots. Their distinctness follows from the original labels and the primitive-root relation, so the pinned Mathlib criterion Matrix.det_vandermonde_ne_zero_iff makes this cofactor nonzero. The adjugate identities then give H(qstar) nonzero, with (B times V(qstar))_i a nonzero scalar multiple of sigma_i(alpha).

Let P prime denote the frozen split-determinant generator in the ideal argument. The existing irreducibility result D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible supplies that P prime is prime over k. Vanishing of a target polynomial on the actual image transfers to the nonempty cofactor chart; multiplying by H makes it vanish on the full zero locus of P prime. The pinned Nullstellensatz identity MvPolynomial.IsPrime.vanishingIdeal_zeroLocus, followed by cancellation of the nonzero chart factor, gives the vanishing ideal of the actual image as the principal ideal (P). Ordinary affine Zariski closed sets are polynomial zero loci, so the affine Zariski closure of the actual image is V(P).

The reused ingredients are the frozen irreducibility and determinant statements above together with the pinned Mathlib suppliers Matrix.mul_adjugate, Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_vandermonde_ne_zero_iff, MvPolynomial.IsPrime.vanishingIdeal_zeroLocus and Ideal.mem_span_singleton. This application records their parameter correspondence and the nonzero-chart boundary; it does not use a rank/Jacobian route, assert the proportionality statement associated with the next equation, or complete the full window classification or trace-dual analysis.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.coefficient_zero_count`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_structure`
- Dependency: [D5/S3/Quantum/Algebra/SplitQuarticIrreducibility](SplitQuarticIrreducibility.md)
