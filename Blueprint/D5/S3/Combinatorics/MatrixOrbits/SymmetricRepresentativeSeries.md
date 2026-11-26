# The generating function for symmetric-representative matrix orbits

## Abstract

The generating function for symmetric-representative matrix orbits

**Theorem 1.1 (The all-degree coefficient formula).**

$$\forall n \in \mathbb{N},\quad\lvert\{C \in O_{n} \mid \exists B \in M_{n}, ([B]=C \land \forall i,j \in I, B_{ij}=B_{ji})\}\rvert = [x^{n}]\frac{1-2x+4x^{2}-x^{3}+9x^{4}+x^{5}+12x^{6}+6x^{8}-x^{9}+x^{10}}{(1-x)^{3}(1-x^{2})(1-x^{3})^{2}(1-x^{4})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MatrixOrbits/SymmetricRepresentativeSeries.source_identity_literal` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a333886-symmetric-matrix-orbits` (proved) by `D5/S3/Combinatorics/MatrixOrbits/SymmetricRepresentativeSeries.source_identity_literal`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a333886-symmetric-matrix-orbits","declaration_gid":"D5/S3/Combinatorics/MatrixOrbits/SymmetricRepresentativeSeries.source_identity_literal","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vladeta Jovovic (2026). *OEIS A333886 generating-function conjecture*. URL: <https://oeis.org/A333886>.

*Commentary.*

For each natural n, let M_n be the four by four matrices of natural numbers whose four row sums and four column sums are all n. Let O_n be the quotient of M_n under the action of the product of two copies of S_4. A row permutation and a column permutation are chosen independently. The class of B is written [B]. A class is counted once when it contains a symmetric B. The indices i and j range over I = {0, 1, 2, 3}. The coefficient and the cardinality equality are in the rationals. The denominator is a unit because its constant coefficient is one. This includes n = 0, where the orbit of the zero matrix contributes one.

Transpose swaps the two permutation factors. In size four, every transpose-fixed orbit has a symmetric representative. The twisted counts split by cycle type with multiplicities 1, 6, 3, 8, and 6. In the identity twist, the minima of the opposite edge pairs split off three common weights. The remaining triangular cases change the maximum weighted degree. The transposition twist first separates equal entries by testing whether the difference size is zero. Equal entries have equal parities. For positive differences, the parity of the size determines which reconstruction of the residual entries applies. The other three twists are direct graded fiber counts. The geometric weights are 1, 2, 3, or 4. Their positivity makes each natural-parameter fiber finite and gives each geometric factor 1 - x^d constant coefficient one, so it is a unit. The published denominator also has constant coefficient one, and 24 is a unit over the rationals. Clearing denominators in the weighted sum gives the identity. The Fin 16 bound in the symmetrizer controls iterates on matrix positions for arbitrary entries and margins.

## References

- Truth anchor: `D5/S3/Combinatorics/MatrixOrbits/SymmetricRepresentativeSeries.source_identity_literal`
