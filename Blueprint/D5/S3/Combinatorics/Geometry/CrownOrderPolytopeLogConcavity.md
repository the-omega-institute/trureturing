# Log-concavity of the full crown f-vector

## Abstract

Every positive crown has a log-concave full geometric face vector.

Conjecture 3.7 concerns the full geometric face vector, including the empty face and the whole polytope. For natural j with j < 2n+2, write F(n,j) for entry j of crownGeometricFVector n, whose index type is Fin (2*n+2). Thus F(n,0)=1 counts the empty face, and F(n,j) for j>0 counts the actual nonempty exposed faces of affine dimension j-1; entry 2n+1 counts the whole polytope. The published face-count formula is proved from this geometry. The auxiliary Chebyshev factorization and corrected Newton inequalities establish log-concavity.

**Theorem 1.1 (Conjecture 3.7 for every positive n).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \left(0 < n \land 0 < k < 2 \cdot n + 1\right) \Rightarrow \operatorname{F}\left(n, k - 1\right) \cdot \operatorname{F}\left(n, k + 1\right) \le \operatorname{F}\left(n, k\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity.crownGeometricFVector_log_concave` (`✓ std3`). ∎

*Resolves.* `Problems/crown-order-polytope-log-concavity` (proved) by `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity.crownGeometricFVector_log_concave`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"crown-order-polytope-log-concavity","declaration_gid":"D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity.crownGeometricFVector_log_concave","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every positive natural n and every natural k with 0 < k < 2n+1, the product of entries k-1 and k+1 of the actual full geometric f-vector is at most the square of entry k. Thus every internal index is covered, including the comparison with the empty face and the comparison with the whole polytope. The statement is the assertion of source Conjecture 3.7 for the full geometric vector.

The proof transports the scalar polynomial to the reals and factors T_n-1 separately for even and odd n. Squared Chebyshev U factors retain repeated-root multiplicities; the odd factor U_m+U_(m-1) divides U_(2m). The upstream Newton inequality applied to the negated root multiset, with Vieta's coefficient formula, gives the strong coefficient inequalities. The index is reversed by the polynomial degree, and coefficients beyond that degree vanish. For n at least two the bounds s_0 >= n^2, s_0 <= s_1 <= 2n s_0 repair all three comparisons affected by the constant and linear corrections. The actual n equals one vector is (1,3,3,1). Only the auxiliary scalar polynomial is shown to split over the reals; no real-rootedness of the actual full f-polynomial is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity.crownGeometricFVector_log_concave`
- Dependency: [D5/S3/Analytic/RealRootedCoefficientNewton](../../Analytic/RealRootedCoefficientNewton.md)
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeChebyshev](CrownOrderPolytopeChebyshev.md)
