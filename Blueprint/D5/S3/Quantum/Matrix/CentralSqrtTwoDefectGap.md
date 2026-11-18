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

Let e_q be the fixed coordinate vector at q. If A is real symmetric, B=A+c e_q e_q^T, and u,v are arbitrary vectors satisfying Au=lambda u and Bv=mu v, then (mu-lambda)<u,v> =c*u(q)*v(q). The identity is proved by the matrix update and symmetry.

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

The fixed matrix family and spectral-separation question are from Childs et al., Exponential algorithmic speedup by a quantum walk, arXiv:quant-ph/0209131v2, Section III.D, Lemma 2. The endpoint proof uses every real energy and requires no asymptotic root enumeration. The spectral conclusion supplies no physical access model, EXIT algorithm, classical oracle lower bound or complete quantum/classical separation.

Finite-time endpoint application. Fix a natural n>=1 and put d=2*n. Let J_n=centralDefect(n), indexed by 0,...,d-1: its diagonal is zero, J_(j,j+1)=J_(j+1,j)=1 except at j=n-1, where both entries are sqrt(2), and all other entries are zero. The formal index Fin(2*n-1+1) has d elements under n>=1. The existing centralEdges and centralDefect definitions use ZeitlinSixJ.Recurrence.jacobiMatrix and upperBand with zero diagonal and these edge weights. Hence J_n is real symmetric. Write W for a real orthogonal eigenvector matrix, with J_n=W diag(lambda_i) W^T. Here i runs through all d indices of the Hermitian spectral enumeration, not a selected band or sector. Matrix.IsHermitian.spectral_theorem and roots_charpoly_eq_eigenvalues identify this enumeration with the complete characteristic-root multiset, including algebraic multiplicities.

Define delta_n=min_(i!=j)|lambda_i-lambda_j| over the full enumeration. There are at least two indices, including when n=1. Apply central_spectral_gap with its parameter m=n-1, so m+1=n, to this actual root enumeration. Every distinct-index distance is at least c/n^3, where c=2*sqrt(2)/(1+sqrt(2))^2>0. Thus delta_n>=c/n^3>0, all eigenvalues are distinct, and delta_n is the actual minimum, independent of the enumeration order. The time hypothesis below uses delta_n itself; it does not replace that minimum by the inverse-cubic lower bound.

Reversal and endpoint weights. Let R send coordinate j to d-1-j. The displayed edge weights are invariant under reversal, so R J_n=J_n R and R^2=I. Set B=W^T R W. Commutation gives (lambda_i-lambda_j)B_ij=0; distinctness makes B diagonal. Since B^2=I, its diagonal entries s_i satisfy s_i^2=1, hence |s_i|=1. From R W=W B, W_(d-1,i)=s_i W_(0,i). Therefore a_i=W_(d-1,i)W_(0,i) and w_i=W_(0,i)^2 satisfy |a_i|=w_i>=0 and sum_i w_i=1, the last identity being the squared norm of row zero of W. These are consequences of the actual matrix, rather than assumed endpoint-pairing data. The needed orthogonality identities are Unitary.coe_star_mul_self and Unitary.coe_mul_star_self; conjugation is the existing Unitary.conjStarAlgAut, with Fin.revPerm representing R.

Spectral evolution and integration. Complexify J_n entrywise and put U(t)=exp((-i*t) J_n) for real t, using the matrix exponential and the negative imaginary phase. The spectral decomposition, Matrix.exp_conj and Matrix.exp_diagonal, with scalar parameter -i*t, give U(t)_(d-1,0)=sum_i a_i exp(-i*lambda_i*t). Every phase and every finite sum, product, squared modulus and real part here is continuous on R; thus it is integrable on each compact interval. The integral from zero to positive T is the ordinary real Lebesgue interval integral. Finite sum interchange, taking real parts and extracting constant coefficients are justified by intervalIntegrable continuity and interval-integral linearity. The existing LidarRestrictedAnticoncentrationRefutation.OpLidarTwinProbability.normSq_finite_sum applies to z_i=a_i exp(-i*lambda_i*t): the squared modulus is sum_(i,j) a_i*a_j Re(exp(-i*(lambda_i-lambda_j)*t)).

Exact off-diagonal mass. Put D=sum_i w_i^2. The diagonal terms integrate to T*D. For i!=j, set x=lambda_i-lambda_j, so |x|>=delta_n>0. The existing integral_exp_mul_complex, with coefficient -i*x and endpoints 0,T, gives integral_0^T exp(-i*x*t) dt =(exp(-i*x*T)-1)/(-i*x). Since each phase has modulus one, its modulus is at most 2/|x|<=2/delta_n. Bounding the real part below by minus the modulus and using |a_i*a_j|=w_i*w_j therefore gives P_T:=T^(-1)*integral_0^T |U(t)_(d-1,0)|^2 dt >=D-[2/(T*delta_n)]*sum_(i!=j) w_i*w_j =D-[2/(T*delta_n)]*(1-D). The equality retains every off-diagonal term: sum_(i!=j) w_i*w_j=(sum_i w_i)^2-sum_i w_i^2=1-D. No coefficient is discarded, including zero weights.

Strict threshold conclusion. Cauchy-Schwarz, in the existing sq_sum_le_card_mul_sum_sq with index set univ and f=w, yields 1=(sum_i w_i)^2<=d*D, hence D>=1/d. The existing sum_sq_le_sq_sum_of_nonneg yields D<=1. For every real epsilon>0 and T>=4*n/(epsilon*delta_n)=2*d/(epsilon*delta_n), positivity of n, epsilon and delta_n gives T>0 and 2/(T*delta_n)<=epsilon/d. Since 1-D>=0, P_T>=D-(epsilon/d)*(1-D). The exact scalar difference is D-(epsilon/d)*(1-D)-(1-epsilon)/d =(D-1/d)*(1+epsilon/d)+epsilon/d^2>0. Consequently T^(-1)*integral_0^T |[exp(-itJ_n)]_(2*n-1,0)|^2 dt >(1-epsilon)/(2*n). The positive surplus epsilon/d^2 preserves strictness at equality in the time threshold, for every epsilon>0 including epsilon>=1, and for n=1; no limiting or generic-parameter exclusion is used.

This is reuse-only application exposition of the existing frozen central-defect results and pinned Mathlib suppliers, following Childs et al., quant-ph/0209131v2, Section III.D, Lemma 1, equations (42)-(49), pages 13-14. It introduces no separate frozen endpoint declaration and makes no mathematical novelty claim. The conclusion concerns this explicit finite matrix and a uniform real-time average. A graph-column realization or intertwining with a graph Hamiltonian requires its own bridge. Physical graph access, an oracle/query cost model, the complete EXIT algorithm and a classical separation each require additional hypotheses and arguments; none follows from this matrix estimate alone.

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
