# Uniform finite-time endpoint probability

## Abstract

Finite-time endpoint transfer for the actual central square-root-two defect path.

**Definition 1.1 (Negative imaginary spectral phase).**

Lean statement: `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.phase`

*Formalization.* `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.phase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

For real x and t, phase(x,t)=exp(-i*x*t), with i the imaginary unit. The modulus is one; no periodicity or integer energy assumption is used.

**Theorem 1.2 (The off-diagonal mass estimate).**

Lean statement: `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.finite_window_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.finite_window_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

Let I be any finite index type, and let a,lambda,w:I->R satisfy |a_i|=w_i and sum_i w_i=1. If delta>0, T>0 and delta<=|lambda_i-lambda_j| whenever i!=j, put D=sum_i w_i^2. Then D-[2/(T*delta)]*(1-D) <= T^(-1)*integral_0^T |sum_i a_i exp(-i*lambda_i*t)|^2 dt. All sums include every index, including zero coefficients. Expanding the squared modulus gives the double sum. Diagonal terms integrate to T*w_i^2. For distinct indices the exponential antiderivative and the triangle inequality bound the modulus of the integral by 2/|lambda_i-lambda_j|<=2/delta. Multiplication by |a_i*a_j| and summation retain the exact off-diagonal mass sum_(i!=j) w_i*w_j=(sum_i w_i)^2-D=1-D. The integral is the ordinary real Lebesgue interval integral; continuity supplies every integrability obligation.

**Definition 1.3 (Complete actual spectrum).**

Lean statement: `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.eigenvalues`

*Formalization.* `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.eigenvalues` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

For every natural n>=1, J_n=centralDefect(n) is the real symmetric matrix indexed 0,...,2*n-1, with zero diagonal, ordinary nearest-neighbour entries 1, central entries J_(n-1,n)=J_(n,n-1)=sqrt(2), and all other entries zero. The formal index Fin(2*n-1+1) has exactly 2*n elements for n>=1. eigenvalues(n) is the real symmetric spectral theorem's complete eigenvalue enumeration; its multiset equals the characteristic-root multiset, retaining all algebraic multiplicities.

**Definition 1.4 (Actual minimum separation).**

Lean statement: `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.spectralGap`

*Formalization.* `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.spectralGap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

spectralGap(n) is min_(i!=j) |lambda_i-lambda_j| for the complete enumeration eigenvalues(n). The finite set is nonempty, including n=1. The actual-matrix spectral gap theorem gives the positive lower bound [2*sqrt(2)/(1+sqrt(2))^2]/n^3 for every pair, so the minimum is positive. The time condition below uses this actual minimum.

**Theorem 1.5 (Strict endpoint probability at the time threshold).**

Lean statement: `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.actual_endpoint_average`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.actual_endpoint_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

For every natural n>=1, real epsilon>0 and real T>=4*n/[epsilon*spectralGap(n)], let U(t)=exp((-i*t) smul complexify(J_n)). Then T^(-1)*integral_0^T |U(t)_(2*n-1,0)|^2 dt >(1-epsilon)/(2*n). No spectrum, endpoint-weight identity or integral estimate is assumed. Reversal commutes with the actual J_n. In its real orthonormal eigenbasis, the positive gap forces the conjugated reversal to be diagonal. Its square is the identity, so each diagonal entry is a sign. Thus the endpoint coefficients a_i have |a_i|=w_i=|W_(0,i)|^2 and sum_i w_i=1. The spectral matrix exponential identifies the endpoint amplitude with sum_i a_i exp(-i*lambda_i*t). Writing d=2*n, Cauchy-Schwarz gives D=sum_i w_i^2>=1/d, while nonnegativity gives D<=1. The preceding estimate and 2/(T*delta)<=epsilon/d give a lower bound D-(epsilon/d)*(1-D). Its difference from (1-epsilon)/d is (D-1/d)*(1+epsilon/d)+epsilon/d^2>0. This includes equality in the time threshold. The conclusion concerns the explicit finite matrix and uniform real-time average. It asserts no graph-column implementation, physical graph access, oracle cost, full EXIT algorithm or classical separation. The estimate follows Childs et al., quant-ph/0209131v2, Section III.D, Lemma 1, equations 42-49; no mathematical novelty is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.actual_endpoint_average`
- Truth anchor: `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.eigenvalues`
- Truth anchor: `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.finite_window_lower_bound`
- Truth anchor: `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.phase`
- Truth anchor: `D5/S3/Quantum/Dynamics/EndpointFiniteWindow.spectralGap`
- Dependency: [D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap](../Matrix/CentralSqrtTwoDefectGap.md)
- Dependency: [D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation](../Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.md)
