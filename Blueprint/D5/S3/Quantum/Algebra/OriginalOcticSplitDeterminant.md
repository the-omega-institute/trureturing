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

For the Auric specialization, take the designated positive real root alpha = 2^(1/8), let D = Q(alpha) inside C, choose zeta = exp(pi i/4), and put K = D(zeta). Fix any Q-algebra homomorphism lambda: K -> k into an algebraically closed characteristic-zero field k with its Q-algebra structure. For each label i, let sigma_i: D -> K be the Q-algebra embedding sending alpha to alpha zeta^i, and put tau_i = lambda composed with sigma_i. Let X be the Q-span of 1, alpha, alpha^3 and alpha^4. The actual quotient set QX consists of u/v with u and v in X and v nonzero; it contains 0 by taking u = 0 and v = 1. Its image S consists of embed(x) = (tau_i(x)) for x in QX. The original labels are ordered 0 through 7, with Fin 8 and ZMod 8 identified by their representatives. Every row and column index below starts at zero.

Let B be the exact eight-by-four matrix whose row i is the four tau_i-values of 1, alpha, alpha^3 and alpha^4, and let P(q) be the determinant of [B | diag(q) B] with those original row labels and the displayed column order. Under the order-preserving identification of Fin 8 and ZMod 8, P is exactly splitDeterminant(B), with only the corresponding renaming of polynomial variables and no determinant sign or scalar change. The forward inclusion is the actual-kernel calculation: for rational coordinates a,b with the denominator element of X nonzero, the vector (-a,b), mapped into k, is a nonzero kernel vector of the evaluated split matrix at q = embed(u/v). Therefore P vanishes on every point of S, including zero.

The reverse direction first transfers rational parameters to arbitrary coefficients in k. Clearing the finitely many linear denominators gives a polynomial identity in two blocks of coefficient variables; the rational coefficient points are Zariski dense because k has characteristic zero. Hence vanishing for every rational numerator and every nonzero rational denominator transfers to every k-valued numerator and denominator for which all eight transported denominators are nonzero.

On the open chart where the determinant vanishes and the cofactor product is nonzero, let M(q) be the evaluated eight-by-eight split matrix and take column indexed 7 of adjugate(M(q)), namely its eighth column. The negatives of its entries indexed 0 through 3 define U, and its entries indexed 4 through 7 define V; set H(q) = product over i of (B times V(q))_i. The identity M times adjugate(M) = det(M) times the identity gives q_i = (B times U(q))_i / (B times V(q))_i whenever P(q) = 0 and H(q) is nonzero. This is the inverse chart used by the rational-parameter transfer.

The chart is nonempty at the square point qstar_i = tau_i(alpha)^2. The determinant is zero because columns indexed 2 and 5, the third and sixth columns, coincide there. Put c = adjugate(M(qstar))_(5,7); this is the signed minor obtained by deleting row indexed 7 and column indexed 5 from M(qstar). The remaining seven-by-seven matrix is a column permutation of a Vandermonde matrix on the transported roots with labels 0 through 6. Their distinctness follows from the original labels and the primitive-root relation, so the pinned Mathlib criterion Matrix.det_vandermonde_ne_zero_iff gives c nonzero. The adjugate identities give (B times V(qstar))_i = c tau_i(alpha); each transported root is nonzero, and hence H(qstar) is nonzero.

The existing irreducibility result D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible makes this same P prime over k. For every polynomial f in the eight variables with arbitrary coefficients in k, vanishing on S transfers to the nonempty cofactor chart. Thus H f vanishes on the full zero locus of P. The pinned Nullstellensatz identity MvPolynomial.IsPrime.vanishingIdeal_zeroLocus gives P dividing H f. Since P(qstar) = 0 and H(qstar) is nonzero, P does not divide H; primality gives P dividing f. Together with the forward inclusion, f vanishes on S if and only if P divides f, so the vanishing ideal of S is exactly the principal ideal (P). For the affine Zariski topology induced from the prime spectrum by the point-evaluation map, closed sets are precisely polynomial ideal zero loci. Consequently the affine Zariski closure of S is V(P).

The reused ingredients are the irreducibility and determinant statements above together with the pinned Mathlib suppliers Matrix.mul_adjugate, Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_vandermonde_ne_zero_iff, MvPolynomial.IsPrime.vanishingIdeal_zeroLocus and Ideal.mem_span_singleton. This application uses one fixed lambda throughout and describes its parameter correspondence and the nonzero-chart boundary. It does not use a rank/Jacobian route, assert the subsequent proportionality statement, or complete the general window classification or trace-dual analysis.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.coefficient_zero_count`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_structure`
- Dependency: [D5/S3/Quantum/Algebra/SplitQuarticIrreducibility](SplitQuarticIrreducibility.md)
