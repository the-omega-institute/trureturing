# The strict rectangular realignment gap

## Abstract

The strict rectangular realignment gap

All matrices act on the complex product space with Alice dimension m and Bob dimension n. Density means positive semidefinite with trace one. The singular multiset contains exactly m squared row singular values of the actual complex realignment, including multiplicities and zeros. The norm is the existing rectangular trace norm, the trace of the positive square root of the column Gram matrix.

The common construction splits Bob into an occupied block of dimension mq and an unused orthogonal block. The entangled term is a Gram matrix whose q columns are the unnormalized maximally entangled vectors in orthogonal multiplicity sectors. Nonnegative scalar identity terms on the two blocks preserve positivity. Identifying the complete Bob index type with Fin n preserves density and the realignment row Gram matrix.

If the entangled, occupied-identity and unused-identity coefficients are t, u and v, the trace is tmq+um squared q+vmr. The realignment row Gram matrix is mu I+nu dd adjoint, where d is the vectorized m by m identity, mu=q times t squared, and nu=q times (2tu plus m times u squared) plus r times v squared. Since the squared norm of d is m, the characteristic polynomial has one factor with root mu+m nu and m squared minus one factors with root mu. The argument computes this polynomial using the scalar shift and rank-one characteristic-polynomial identities, then obtains actual native singular values by taking square roots of its roots. Rectangular adjoint invariance identifies their sum with the actual trace norm.

**Theorem 1.1 (The uniform spectrum in all sufficiently large Bob dimensions).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.uniform_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.uniform_witness` (`✓ std3`). ∎

*Citation.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For every natural m at least two and n at least m cubed, there exists a positive semidefinite trace-one complex bipartite matrix whose actual realignment trace norm is exactly one. Put a=1/m squared and b=(1-a)/(m squared minus one). Its complete singular multiset is one copy of a and m squared minus one copies of b; in this case b=a. The construction takes q=m squared, coefficient t=1/m cubed, and zero coefficients on both identity terms. Additional Bob coordinates carry zero weight. The row Gram matrix is I/m to the fourth, so every row singular value is exactly 1/m squared.

**Theorem 1.2 (The main prescribed spectrum below the final tensor block).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.main_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.main_witness` (`✓ std3`). ∎

*Citation.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For natural dimensions with 2 at most m, m strictly less than n, and n strictly less than m cubed minus m, let a=1/sqrt(mn) and b=(1-a)/(m squared minus one). There exists a positive semidefinite trace-one complex matrix with realignment trace norm exactly one and complete singular multiset consisting of one a and m squared minus one copies of b.

Write n=mq+r with 0 at most r less than m. The coefficients are t=b/sqrt(q), u=a squared minus b/(m sqrt(q)), and v=a squared. The dimension bound gives n at most m squared sqrt(q), which implies u is nonnegative. The endpoint q=m squared minus two is treated by its exact polynomial inequality; smaller q use the integral remainder slack. The identities a squared mn=1 and (m squared minus one)b+a=1 give trace one and singular-value sum one. The computed Gram parameters satisfy mu=b squared and mu+m nu=a squared. The construction is the Li-Poon-Sze family, used here on a convenient sufficient range.

**Theorem 1.3 (A supported spectrum with an arbitrary unused Bob complement).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.supported_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.supported_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For natural m, q and n with m at least two, 1 at most q at most m squared, and mq at most n, let a=1/(m sqrt(q)) and b=(1-a)/(m squared minus one). There exists a positive semidefinite trace-one complex matrix whose realignment trace norm is exactly one and whose complete singular multiset is one copy of a and m squared minus one copies of b. No condition on the size of the unused Bob complement is imposed.

Use the same entangled and occupied-identity coefficients t=b/sqrt(q) and u=a squared minus b/(m sqrt(q)), with v=0 on the unused complement. The inequality sqrt(q) at most m gives positivity. The identity a squared m squared q=1 gives trace one and the distinguished squared singular value. Taking q=m squared minus one yields the supported family used near the cubic dimensional transition, with first singular value 1/(m sqrt(m squared minus one)). The zero complement does not change the row Gram matrix or any row singular value. This statement retains the full dimensional family, rather than assuming a spectrum can be realized.

**Theorem 1.4 (Strict separation at every nontrivial elementary symmetric order).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.result` (`✓ std3`). ∎

*Resolves.* `Problems/li-poon-sze-2011-p2-realignment-gap` (proved) by `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"li-poon-sze-2011-p2-realignment-gap","declaration_gid":"D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every pair of natural local dimensions 2 at most m strictly less than n, and every natural order ell from two through m squared, there is an actual complex bipartite density matrix whose realignment has nuclear norm at most one and whose degree ell elementary symmetric singular-value function is strictly greater than a single real constant bounding that function on every separable state. Density means positive semidefinite with trace one. Separability means a finite convex combination of product density matrices.

The constant is the one-heavy-coordinate profile at delta=1-sqrt((1-1/m)(1-1/n)). For each separable density, CCNR bounds the total of its m squared row singular values by one. The covariance estimate bounds the sum after the first by sqrt((1-Tr(rho_A squared))(1-Tr(rho_B squared))); the marginal purity bounds Tr(rho_A squared) at least 1/m and Tr(rho_B squared) at least 1/n give the dimension-only tail budget 1-delta. No separability premise is assumed for the constructed witness.

Complete trace-product normalized Hermitian bases are constructed from the real dimension of the Hermitian matrix space and an orthonormal basis. Let U and V have their flattened local matrices as columns, and C be the existing real correlation matrix of the same actual separable density. Coordinate reconstruction and the finite product decomposition prove the exact complex matrix identity R(rho)=U C V transpose, with U adjoint times U and V adjoint times V equal to identity. The actual row Gram is U times the complex scalar extension of C C transpose times U adjoint. Equality of characteristic polynomials after scalar extension, followed by mapping polynomial roots and sorting eigenvalues, proves equality of the complete descending singular vectors, including all zeros. The spectral bridge is proved rather than added as a hypothesis.

On the real correlation carrier, the existing finite weighted rank-one nuclear bound, Parseval identity and local purity at most one prove CCNR. The existing covariance estimate correlation_tail_corrected and the marginal dimension purity bounds give the tail constraint. The identity tail=nuclear norm-operator norm transfers this constraint to C transpose, because both norms are invariant under real transposition. The exact complex spectral bridge transfers both inequalities back to the actual realignment. Local bases are chosen inside the proof and do not restrict the theorem's quantified states.

Increase the first singular coordinate to complete total mass one. Newton and Maclaurin inequalities bound both remaining elementary symmetric terms by equal-tail terms. The resulting profile is strictly decreasing from the uniform coordinate to one. The covariance threshold exceeds the leading coordinate of each constructed witness.

Below the last supported block the main Li-Poon-Sze matrix has spectrum alpha once and beta repeated m squared minus one times, with alpha=1/sqrt(mn) and beta=(1-alpha)/(m squared minus one). Integer remainder slack guarantees its positive identity coefficient. In the supported band use q=m squared minus one occupied multiplicity sectors and append zero coordinates on Bob. Its leading coordinate is 1/(m sqrt(q)). For m=2 the rational comparison 1/(2sqrt(3)) less than 7/24 less than delta treats the small endpoint. At and above n=m cubed the explicit uniform witness has every singular value equal to 1/m squared.

Every witness is an actual positive normalized block matrix. Its realignment row Gram is scalar plus the outer product of the flattened identity, so its characteristic polynomial determines the complete singular multiset. The established rectangular nuclear norm agrees with the sum of these row singular values and equals one for each witness. No prescribed-spectrum or scalar feasibility assumption is added to the final statement.

The covariance inequality and the main and uniform Li-Poon-Sze constructions are existing literature. The supported interpolation and their combination with the general covariance tail budget give the rectangular gap. Together with the source's equal-dimensional equality this answers its comparison question. Exact extremal values from the separate question remain outside the conclusion, as do unrestricted replacements for all filter-normal-form bounds.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.main_witness`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.supported_witness`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.uniform_witness`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks](../PermutationCriteria/BellBlocks.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance](CorrelationMinorNormCovariance.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound](RealignmentSchurBound.md)
