# Central square-root-two defect gap

## Abstract

Rank-one sector separation for the central square-root-two defect Jacobi family.

**Theorem 1.1 (Inverse gap from endpoint control).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_from_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_from_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

For real c,K,lambda,mu,x,y,z with c>0, K>0, (lambda-mu)z=cxy, 1<=K*x^2, 1<=K*y^2, and |z|<=1, one has c/K<=|lambda-mu|. This is the quantitative inverse-cubic bridge once K is the endpoint control constant.

**Theorem 1.2 (Rank-one cross-sector identity).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_cross_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_cross_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

If A is real symmetric, B=A+c vv^T with v the coordinate vector at q, and Au=lambda u, Bv=mu v, then (mu-lambda)<u,v> =c*u(q)*v(q). The identity is proved by the matrix update and symmetry.

**Theorem 1.3 (Rank-one cross-sector gap).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_of_matrices`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_of_matrices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

Combining the preceding identity with endpoint controls 1<=K*u(q)^2 and 1<=K*v(q)^2 and |<u,v>|<=1 gives c/K<=|lambda-mu| for actual eigenpairs of the two symmetric matrices.

**Definition 1.4 (Central square-root-two edge sequence).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralEdges`

*Formalization.* `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralEdges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

For n>=1, centralEdges(n) is the edge sequence on Fin(2*n-1+1) whose unique central entry at n-1 is sqrt(2), with every other entry 1; the displayed dimension is 2*n under the stated threshold.

**Definition 1.5 (Actual central defect Jacobi matrix).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralDefect`

*Formalization.* `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralDefect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

centralDefect(n) is the zero-diagonal Jacobi matrix of dimension 2*n-1+1 with nearest-neighbour entries centralEdges(n), hence exactly the fixed central-sqrt(2) defect matrix from the source event after the threshold identification.

**Theorem 1.6 (Uniform endpoint observability).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.recurrence_endpoint_observability`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.recurrence_endpoint_observability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

Let n>=1 and y(0)=0. Suppose y(j+2)=t*y(j+1)-y(j) for j+2<=n+1 and y(n+1)=b*y(n). Then the sum of y(j)^2 over 1<=j<=n is at most (1+|b|)^2*n^3*y(n)^2. The estimate holds for every real t, including both band edges and the exterior regimes. Inside |t|<=2, the finite continuant formula and the Chebyshev bound |U_k(x)|<=k+1 control the backward recurrence. Outside the band, the forward coordinate magnitudes are nondecreasing.

**Definition 1.7 (Concrete reflection sector).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sectorMatrix`

*Formalization.* `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sectorMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

sectorMatrix(n,b) is the unit-edge path on n+1 vertices, with diagonal zero except for the last entry b.

**Theorem 1.8 (Sector eigenvector endpoint bound).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sector_endpoint_observability`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sector_endpoint_observability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

For every eigenpair sectorMatrix(n,b)*v=t*v, the sum of v(i)^2 is at most (1+|b|)^2*(n+1)^3*v(n)^2. No normalization, nonzero endpoint, band location or eigenvalue separation is assumed.

**Theorem 1.9 (Opposite-sector inverse-cubic gap).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sector_inverse_cubic_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sector_inverse_cubic_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

For unit eigenvectors of sectorMatrix(n,-sqrt(2)) and sectorMatrix(n,sqrt(2)), with eigenvalues lambda and mu, their distance is at least [2*sqrt(2)/(1+sqrt(2))^2]/(n+1)^3. This bound is uniform over all opposite-sector pairs, including exterior modes. It does not by itself bound pairs belonging to the same sector.

**Definition 1.10 (Complete reflection-sector spectrum).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sectorSpectrum`

*Formalization.* `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sectorSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

sectorSpectrum(n) joins the two Hermitian eigenvalue enumerations of the n+1 dimensional sectors. The sum type retains every index and every algebraic multiplicity.

**Theorem 1.11 (All-pair sector-union gap).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sector_spectral_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sector_spectral_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

Any two distinct indices in the complete sector union have eigenvalue distance at least [2*sqrt(2)/(1+sqrt(2))^2]/(n+1)^3. Positive-index monotonicity and rank-one subadditivity constrain each threshold count difference to zero or one. Two same-sector indices closer than the cross-sector bound would force a count difference of at least two.

**Theorem 1.12 (Actual full-matrix algebraic gap).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.central_spectral_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.central_spectral_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

For every enumeration of all characteristic roots of centralDefect(n+1), distinct indices have distance at least [2*sqrt(2)/(1+sqrt(2))^2]/(n+1)^3. Folding the path at the defect gives two identical free-path blocks coupled at their endpoints. The sum and difference bases conjugate this matrix to the two Robin sectors. Characteristic-polynomial factorization identifies the whole algebraic root multiset with the sector union; injectivity follows from the quantitative gap.

**Theorem 1.13 (Uniform gap of the fixed defect family).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.uniform_inverse_cubic_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.uniform_inverse_cubic_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

There are c>0 and N>=1 such that for every n>=N the actual defect matrix is Hermitian and every algebraic eigenvalue enumeration satisfies |lambda(i)-lambda(j)|>=c/n^3 at distinct indices. One may take c=2*sqrt(2)/(1+sqrt(2))^2 and N=1. The Fin(2*n-1+1) index type has exactly 2*n elements under n>=1.

The fixed matrix family and spectral-separation question are from Childs et al., Exponential algorithmic speedup by a quantum walk, arXiv:quant-ph/0209131v2, Section III.4, Lemma 2. The endpoint proof uses every real energy and requires no asymptotic root enumeration. The spectral conclusion supplies no physical access model, EXIT algorithm, classical oracle lower bound or complete quantum/classical separation.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralDefect`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralEdges`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.central_spectral_gap`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_cross_identity`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_from_identity`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_of_matrices`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.recurrence_endpoint_observability`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sectorMatrix`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sectorSpectrum`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sector_endpoint_observability`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sector_inverse_cubic_gap`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.sector_spectral_gap`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.uniform_inverse_cubic_gap`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence](../../Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.md)
- Dependency: [D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum](GibbsStochasticSimpleSpectrum.md)
