# Supported Huang eigenvectors on 258 cube vertices

## Abstract

Any 258 selected vertices of Q9 support at least two dimensions of real functions with Huang eigenvalue +3.

The functions are on the actual Boolean vertices of Q9. The matrix is the original huangMatrix from HypercubeSubQuorum and Archive.Sensitivity, using the same FALSE-prefix convention as BalancedCriticalSpectrum. TRUE selects the first recursive block. The positive eigenvalue is +3; vector entries are arbitrary real numbers. No degree, regularity, balance or connectedness hypothesis is needed for these linear-algebra interfaces.

The external motivation is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7, Problem 2: determine f₂(Q₉)=3 or 4, at https://arxiv.org/html/2610.09483v1#Thmproblem2 . The module reuses the existing Huang family and rank-nullity mechanism to supply inputs for actual component extraction. It makes no novelty, 258-vertex witness, exclusion or solution claim. Component extraction and a possible 96-vertex core bound are separate downstream work, with no acceptance claim made here.

**Definition 1.1 (The actual supported +3 eigenspace).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.supportedEigenSpace`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.supportedEigenSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For U : Finset (Q 9), this real submodule consists exactly of functions z with huangMatrix 9 acting by 3z and z(x)=0 whenever x is outside U. Support may be a proper subset of U. The helper mem_supportedEigenSpace_iff exposes this carrier and is consumed by both vector-extraction interfaces.

**Theorem 1.2 (258 selected vertices leave dimension at least two).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.two_le_finrank_supportedEigenSpace`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.two_le_finrank_supportedEigenSpace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sole assumption is U.card=258. Archive.Sensitivity.g 8 is injective from V 8, of dimension 256, and f_image_g gives eigenvalue sqrt(9)=3. The existing coeff 9 linear equivalence and matrix_coeff transport this family to the original Huang matrix on actual Q9 functions. Restrict these functions to the 512-258=254 coordinates outside U. Rank-nullity gives a kernel of dimension at least two. Its injective coordinate map into supportedEigenSpace U proves the stated lower bound. This reuses the existing positive family without assuming the desired supported dimension.

**Theorem 1.3 (A nonzero actual supported eigenvector).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.exists_nonzero_supported_eigenvector`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.exists_nonzero_supported_eigenvector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For U.card=258, extract a nonzero real function z, zero outside U, with the full ambient equation huangMatrix 9 times z = 3z. It follows from the dimension lower bound and supplies the first vector for the component consumer. No component or sign-switching conclusion is assumed or supplied by this helper.

**Theorem 1.4 (A nonzero supported eigenvector vanishing at any specified vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.exists_nonzero_supported_eigenvector_vanishing_at`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.exists_nonzero_supported_eigenvector_vanishing_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For U.card=258 and every specified actual vertex x of Q9, there is a nonzero function w, zero outside U, satisfying the same full +3 eigen-equation and w(x)=0. The vertex x need not belong to U. Evaluation at x maps the supported space to the one-dimensional real field; a domain of dimension at least two gives a nonzero evaluation kernel. The downstream component argument can therefore zero its chosen root while retaining a nonzero vector; propagation along paths belongs to the separate saturation proof.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.exists_nonzero_supported_eigenvector`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.exists_nonzero_supported_eigenvector_vanishing_at`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.supportedEigenSpace`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.two_le_finrank_supportedEigenSpace`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](BalancedCriticalSpectrum.md)
