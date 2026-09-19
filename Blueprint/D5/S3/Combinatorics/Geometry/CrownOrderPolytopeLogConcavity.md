# Log-concavity of the full crown f-vector

## Abstract

Every positive crown has a log-concave full geometric face vector.

Conjecture 3.7 concerns the full geometric face vector, including the empty face and the whole polytope. The published face-count formula supplies the starting coefficients; the auxiliary Chebyshev factorization and corrected Newton inequalities establish their log-concavity.

**Theorem 1.1 (Conjecture 3.7 for every positive n).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity.crownGeometricFVector_log_concave`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity.crownGeometricFVector_log_concave` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every positive natural n and every natural k with 0 < k < 2n+1, the product of entries k-1 and k+1 of the actual full geometric f-vector is at most the square of entry k. Thus every internal index is covered, including the comparison with the empty face and the comparison with the whole polytope. The statement is the assertion of source Conjecture 3.7 for the full geometric vector.

The proof transports the scalar polynomial to the reals and factors T_n-1 separately for even and odd n. Squared Chebyshev U factors retain repeated-root multiplicities; the odd factor U_m+U_(m-1) divides U_(2m). Rolle's theorem and Laguerre positivity give the strong coefficient Newton inequalities. For n at least two the bounds s_0 >= n^2, s_0 <= s_1 <= 2n s_0 repair all three comparisons affected by the constant and linear corrections. The actual n equals one vector is (1,3,3,1). Only the auxiliary scalar polynomial is shown to split over the reals; no real-rootedness of the actual full f-polynomial is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity.crownGeometricFVector_log_concave`
- Dependency: [D5/S3/Analytic/RealRootedCoefficientNewton](../../Analytic/RealRootedCoefficientNewton.md)
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeChebyshev](CrownOrderPolytopeChebyshev.md)
