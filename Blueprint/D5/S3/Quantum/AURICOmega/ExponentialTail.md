# Exponential remainder

## Abstract

A geometric estimate for the analytic exponential remainder in a complete normed real algebra.

**Theorem 1.1 (A bound from successive factorial ratios).**

$$\forall B \in \operatorname{Type}\left(\right),\; [\operatorname{NormedRing}\left(B\right)] [\operatorname{NormedAlgebra}\left(\mathbb{R}, B\right)] [\operatorname{CompleteSpace}\left(B\right)] [\operatorname{NormOneClass}\left(B\right)] \forall x \in B, r \in \mathbb{R}, n \in \mathbb{N},\; \left(0 \le r \land \left(\operatorname{norm}\left(x\right) \le r \land r < n + 1\right)\right) \Rightarrow \operatorname{norm}\left(\operatorname{exponentialRemainder}\left(x, n\right)\right) \le \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{power}\left(r, n\right), \operatorname{factorial}\left(n\right)\right), \operatorname{subtract}\left(1, \operatorname{divide}\left(r, n + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/ExponentialTail.exp_remainder_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write exponentialRemainder(x,n)=exp(x)-sum from k=0 to n-1 of x^k/k!. Let B be a complete normed real algebra with a submultiplicative norm and norm of the identity equal to one. For a nonnegative r with norm(x) at most r, and r<n+1, the omitted terms of the exponential series have norms bounded by r^n/n! times (r/(n+1))^k. Summing this geometric majorant gives the displayed bound.

Mathlib supplies convergence of the exponential power series, the comparison theorem for sums in normed groups, and the sum of the geometric series. The factorial coefficient estimate joins these results without commuting products. For matrices, the induced maximum row-sum norm is submultiplicative and fits these assumptions; the entrywise maximum norm does not supply that multiplication estimate.

At r=2 and n=13 the ratio is 1/7, so the bound is (7/6) times 2^13/13!. The estimate concerns the actual exponential, rather than only a finite polynomial.

## The actual five-mode walk at two thirds

The mode order is (N,2,3,5,25), with N indexed by 0. The real generator is A=[[0,1,1,1,0],[-1,0,0,0,-1],[-1,0,0,0,0],[-1,0,0,0,-1],[0,1,0,1,0]]. Put X=(2/3)A, O=exp(X), and S=sum from k=0 to 12 of X^k/k!. The transpose relation A^T=-A and Mathlib's matrix exponential product theorem give both orthogonality identities.

The matrix norm throughout the remainder estimate is the induced maximum row-sum norm. Its bound for X is 2. The general exponential remainder theorem gives norm(O-S) at most (7/6) times 2^13/13!, equal to 4/2606175. The successive scalar majorant ratios are at most 1/7. This is smaller than 64/6081075.

The first row of S is exactly [107738440637/248594813775,490347766/1104865839,4899328858/9207215325,490347766/1104865839,-91371050044/248594813775]. Its absolute entries all exceed 367/1000. Subtracting the proved analytic remainder gives absolute entries of the actual O strictly greater than 9/25. Their squares exceed 1/8 and sum to one. The notation squareSum(v) denotes the sum of the five squared coordinates, and minimumSquaredCoordinate(v) denotes their finite minimum.

The coordinates of v=O^T e_N are the entries of the first row of the actual O, so v is a unit vector with full support. Since Fin 5 is nonempty and finite, its minimum squared coordinate exceeds 1/8. The real coordinate calculation is used within the full complex Hilbert space; it imposes no restriction to real input density matrices. The diagonal frame D=diag(1,i,i,i,1) is a passive change of coordinates. The wait 2/3 is a nonnegative mathematical parameter and supplies no physical calibration or additional operation.

Connected-probe rigidity is the standard result of Mayer and Knill, Quantum Process Fidelity Bounds from Sets of Input States, arXiv:1805.04491v1, Theorem 1. Measurement-relative compression uses the common encoder and decoder model of Bluhm, Rauber and Wolf, arXiv:1708.04898v4. Koashi and Imoto, quant-ph/0101144, provide broader no-disturbance structure. The present statement supplies the analytic probe bounds; channel rigidity and compression bounds require their own channel and port hypotheses.

$$
\operatorname{transpose}\left(\operatorname{actualFiveModeExponential}\left(\frac{2}{3}\right)\right) \cdot \operatorname{actualFiveModeExponential}\left(\frac{2}{3}\right) = 1 \land \left(\operatorname{actualFiveModeExponential}\left(\frac{2}{3}\right) \cdot \operatorname{transpose}\left(\operatorname{actualFiveModeExponential}\left(\frac{2}{3}\right)\right) = 1 \land \left(\left\lVert \operatorname{actualFiveModeExponential}\left(\frac{2}{3}\right) - \operatorname{actualFiveModeTaylor}\left(\frac{2}{3}, 13\right) \right\rVert \le \frac{\frac{7}{6} \cdot 2^{13}}{\operatorname{factorial}\left(13\right)} \land \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \frac{9}{25} < \left|\operatorname{coordinate}\left(\operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{actualFiveModeExponential}\left(\frac{2}{3}\right)\right), \operatorname{basisVector}\left(5, 0\right)\right), j\right)\right|\right) \land \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \frac{1}{8} < \operatorname{coordinate}\left(\operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{actualFiveModeExponential}\left(\frac{2}{3}\right)\right), \operatorname{basisVector}\left(5, 0\right)\right), j\right)^{2}\right) \land \left(\frac{1}{8} < \operatorname{minimumSquaredCoordinate}\left(\operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{actualFiveModeExponential}\left(\frac{2}{3}\right)\right), \operatorname{basisVector}\left(5, 0\right)\right)\right) \land \operatorname{squareSum}\left(\operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{actualFiveModeExponential}\left(\frac{2}{3}\right)\right), \operatorname{basisVector}\left(5, 0\right)\right)\right) = 1\right)\right)\right)\right)\right)
$$

### Application to the actual two-setting channel and compression port

Keep the mode order (N,2,3,5,25). Let K be the real symmetric adjacency matrix with undirected edges N-2, N-3, N-5, 2-25, and 5-25, each of weight one. Set D=diag(1,i,i,i,1), U(t)=exp(-itK), O(t)=exp(tA), and W(t)=ofReal(O(t)), where ofReal acts entrywise. The displayed A satisfies D adjoint times (-iK) times D = A. Thus D adjoint times U(t) times D = W(t) for every real t. Conjugation by D and its adjoint gives mutually inverse canonical CPTP maps on all complex density states. Because D is diagonal, this passive coordinate change preserves every mode probability.

$$
\operatorname{adjoint}\left(D\right) \cdot \operatorname{U}\left(t\right) \cdot D = \operatorname{W}\left(t\right)
$$

For each of the two nonnegative waits t=0 and t=2/3, use every mode outcome s. With Pi_s=e_s e_s adjoint, the physical effects are U(t) adjoint times Pi_s times U(t); they are Hermitian idempotents and sum to identity. Their passive-frame representatives are W(t) adjoint times Pi_s times W(t)=ofReal(O(t) transpose times Pi_s times O(t)). For a physical density D rho D adjoint, their probabilities equal p_t(rho)_s=(W(t) rho W(t) adjoint)_{ss}, with rho ranging over all complex density matrices. In particular W(0)=I, and the pulled-back N effect at wait 2/3 is the rank-one projection of v=ofReal(O(2/3) transpose e_N).

The preceding analytic remainder calculation gives sum_j |v_j|^2=1 and |v_j|^2>1/8 for all five coordinates. The five probes (v,e_2,e_3,e_5,e_25) are unit vectors. The four coordinate probes are mutually orthogonal, and v has nonzero overlap with each one, so their nonorthogonality graph is exactly a connected four-spoke star. They span the entire complex five-dimensional space: the nonzero N coordinate of v recovers the omitted e_N direction.

Suppose a canonical CPTP endomorphism T preserves all outcome probabilities at both actual settings for every complex density input. It then preserves the probabilities of these five probes. Apply connected_probability_preserving_identity from `D5/B/S3/Quantum/Reduction/ProbeComponentRigidity` through the canonical finite Kraus representation. It follows that T(X)=X for every complex matrix X. The conclusion uses the complete density-input hypothesis, not a finite sample of calibration states.

Let q be any natural number, let F be any finite classical flag carrier, and let E:M_5(C) to M_(F times Fin q)(C) and R in the reverse direction be canonical CPTP maps. Require E to have classical block-diagonal output on every matrix input. Use the same E and R at both settings; flag probabilities may depend on the input, and F has no uniform cardinality bound. Exact preservation implies 5<=q by canonical_flag_port_lower_bound from `D5/B/S3/Quantum/Reduction/CanonicalFlagCompression` because the connected component of the five probes has dimension five. All input-dependent quantum information passes through Fin q.

For the quantitative statement, define epsilon(E,R) as the supremum over all complex density inputs of the maximum of the two total-variation errors, at waits 0 and 2/3, between the input and the common composite R composed with E. Total variation is half the sum of the five absolute probability differences. Canonical_flag_port_factorization supplies a normalized same-flag Kraus port with identical composite action on every matrix. Its encoder branch index is (F times Fin q) times Fin 5 and its decoder branch index is Fin 5 times (F times Fin q). Reading the same fields as a SparseProbePortBound.Port only reorders finite sums.

$$
\operatorname{epsilon}\left(E, R\right) = \operatorname{sSup}\left(\left\{\operatorname{max}\left(\operatorname{TV}\left(\operatorname{p}\left(0, \rho\right), \operatorname{p}\left(0, \operatorname{compose}\left(R, E, \rho\right)\right)\right), \operatorname{TV}\left(\operatorname{p}\left(\frac{2}{3}, \rho\right), \operatorname{p}\left(\frac{2}{3}, \operatorname{compose}\left(R, E, \rho\right)\right)\right)\right) \mid \rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(5\right)\right)\right\}\right)
$$

Apply sparse_probe_port_bound from `D5/B/S3/Quantum/QuantumChannels/SparseProbePortBound` with d=5, U=W(2/3), r=N=0, and mu=1/8. The row condition U_{N,j}=conj(v_j), unitarity, unit norm, and the pointwise support bound are supplied by the preceding exact calculation. The quantitative argument uses six survival tests: all five coordinate inputs and v. It gives the following uniform bound for every allowed canonical port with 1<=q<=5.

$$
\frac{5 - q}{102} \le \operatorname{epsilon}\left(E, R\right)
$$

Indeed mu(5-q)/((2+mu)(5+1))=(5-q)/102. Let C_q be the set of these epsilon(E,R) over all finite F and allowed canonical E,R. This set is nonempty for every positive q: coordinate measurement followed by storage of the outcome in the classical flag and preparation through one fixed quantum coordinate gives a normalized port. The uniform bound therefore passes to inf C_q. At q=5, a single-flag identity encoder and decoder attain zero error, so inf C_5=0 and the exact minimum coherent dimension is five. The same lower bound and attained-zero conclusion hold for the supplier's finite dependent-family Kraus-port error set.

$$
\frac{5 - q}{102} \le \operatorname{infCanonicalErrors}\left(q\right) \land \operatorname{infCanonicalErrors}\left(5\right) = 0
$$

These are composed applications of the analytic remainder calculation, connected-probe rigidity, canonical flagged-port factorization, and sparse-probe estimate. They assert neither optimality of the lower bound for q<5 nor a physical calibration theorem. The passive frame does not add an operation to the two-wait menu. The cited suppliers retain their own assumptions and literature attribution.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/ExponentialTail.exp_remainder_le`
