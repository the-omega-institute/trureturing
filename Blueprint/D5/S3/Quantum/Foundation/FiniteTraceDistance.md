# Finite Trace Distance

## Abstract

Trace norm, actual density-state distance, and contraction for every canonical quantum channel.

DensityState and QuantumChannel are the canonical FiniteStateChannel carriers. raw denotes CStarMatrix.ofMatrix.symm, applied to the value of a state when its argument is a density state; toCstar denotes the forward equivalence. FiniteType denotes a finite coordinate type with decidable equality, including the empty type. Explicit Type binders carry only the displayed instances. RCLike is the existing Mathlib scalar interface. Adjoint means conjugate transpose and the square root uses the positive-semidefinite matrix order.

**Theorem 1.1 (The Gram matrix computes transformed inner products).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)]\forall A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right), v \in n \to \mathbb{C}, w \in n \to \mathbb{C},\; \operatorname{inner}\left(\mathbb{C}, \operatorname{WithLp.toLp}(2, \operatorname{Matrix.mulVec}(A, v)), \operatorname{WithLp.toLp}(2, \operatorname{Matrix.mulVec}(A, w))\right) = \operatorname{dotProduct}\left(\operatorname{star}\left(v\right), \operatorname{Matrix.mulVec}(A^{*} \cdot A, w)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.inner_A_mulVec_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite coordinate type and complex square matrix A, the inner product of A v and A w is the quadratic pairing of v and w through the Gram matrix A* A. The vectors are equipped with the Euclidean inner product by WithLp.toLp 2. No invertibility, normalization or decidable equality is required.

**Theorem 1.2 (Singular value decomposition).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)][\operatorname{DecidableEq}\left(n\right)]\forall A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \text{let } hH:\operatorname{Matrix.IsHermitian}(\operatorname{Matrix.conjTranspose}(A) \cdot A),\exists V \in \operatorname{Matrix.unitaryGroup}(n, \mathbb{C}), W \in \operatorname{Matrix.unitaryGroup}(n, \mathbb{C}),\; A = \operatorname{val}\left(V\right) \cdot \operatorname{Matrix.diagonal}(\lambda(i:n)\mapsto\operatorname{Complex.ofReal}(\operatorname{Real.sqrt}(\operatorname{Matrix.IsHermitian.eigenvalues}(hH, i)))) \cdot \operatorname{Matrix.conjTranspose}(\operatorname{val}\left(W\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.exists_svd_sqrt_eigenvalues` (`✓ std3`). ∎

*Citation.* Alex Meiburg (2025). *Finite matrix singular value decomposition in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/6a09b2d1761a0d4430083045a247eb121d8da260/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean>.

*Commentary.*

For every finite complex square matrix, two unitary factors give a diagonal singular-value decomposition. The diagonal entries are the real square roots of the eigenvalues of its Gram matrix. The let-bound hH is the canonical Hermitian proof for that Gram matrix; ofReal denotes the real-to-complex embedding. The retained proof is Alex Meiburg's Physlib SVD.

**Theorem 1.3 (The trace of a Hermitian matrix is real).**

$$\forall n \in Type, R \in Type,\; [\operatorname{Fintype}\left(n\right)][\operatorname{RCLike}\left(R\right)]\forall A \in \operatorname{Matrix}\left(n, n, R\right),\; \operatorname{Matrix.IsHermitian}(A) \Rightarrow (\operatorname{RCLike.re}(\operatorname{Matrix.trace}(A)):R) = \operatorname{Matrix.trace}(A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.re_trace_eq_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Hermitian square matrix over an RCLike scalar type, coercing the real part of its trace back to that scalar type gives the original trace. Only the index type is assumed finite; no decidable equality is required.

**Definition 1.4 (Actual trace norm).**

$$\forall m \in FiniteType, n \in FiniteType, R \in RCLike, A \in \operatorname{Matrix}\left(m, n, R\right),\; \operatorname{traceNorm}\left(A\right) = \operatorname{re}\left(\operatorname{trace}\left(\operatorname{sqrt}\left(A^{*} \cdot A\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm` (`✓ std3`).

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

This is the real part of the trace of the positive square root of the Gram matrix.

**Theorem 1.5 (Negation invariance).**

$$\forall m \in FiniteType, n \in FiniteType, R \in RCLike, A \in \operatorname{Matrix}\left(m, n, R\right),\; \operatorname{traceNorm}\left(0 - A\right) = \operatorname{traceNorm}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_neg` (`✓ std3`). ∎

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

Negation leaves the Gram matrix unchanged.

**Theorem 1.6 (Nonnegative trace norm).**

$$\forall m \in FiniteType, n \in FiniteType, R \in RCLike, A \in \operatorname{Matrix}\left(m, n, R\right),\; 0 \le \operatorname{traceNorm}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_nonneg` (`✓ std3`). ∎

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

The positive square root is positive semidefinite and has nonnegative real trace.

**Theorem 1.7 (Unitary maximum formula).**

$$\forall n \in FiniteType, A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \left(\exists U \in \operatorname{unitaryGroup}\left(n, \mathbb{C}\right),\; \operatorname{re}\left(\operatorname{trace}\left(\operatorname{val}\left(U\right) \cdot A\right)\right) = \operatorname{traceNorm}\left(A\right)\right) \land \left(\forall U \in \operatorname{unitaryGroup}\left(n, \mathbb{C}\right),\; \operatorname{re}\left(\operatorname{trace}\left(\operatorname{val}\left(U\right) \cdot A\right)\right) \le \operatorname{traceNorm}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_eq_max_re_tr_U` (`✓ std3`). ∎

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

A unitary attains the trace norm as the real trace of its product with A, and every unitary gives a value at most the trace norm. Here val denotes the underlying matrix. The formula holds in every finite complex square dimension, including the empty type.

**Theorem 1.8 (Trace norm triangle inequality).**

$$\forall n \in FiniteType, A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right), B \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{traceNorm}\left(A + B\right) \le \operatorname{traceNorm}\left(A\right) + \operatorname{traceNorm}\left(B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_add_le` (`✓ std3`). ∎

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

The retained SVD proof identifies the norm as the maximum real trace over unitaries; trace additivity gives the bound.

**Theorem 1.9 (Positive trace norm).**

$$\forall n \in FiniteType, R \in RCLike, A \in \operatorname{Matrix}\left(n, n, R\right),\; \operatorname{PosSemidef}\left(A\right) \Rightarrow \operatorname{embed}\left(R, \operatorname{traceNorm}\left(A\right)\right) = \operatorname{trace}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_of_posSemidef` (`✓ std3`). ∎

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

For a positive semidefinite matrix, the Gram matrix is its square and its positive square root is the original matrix.

**Definition 1.10 (Canonical channel on matrix coordinates).**

$$\forall n \in FiniteType, C \in \operatorname{QuantumChannel}\left(n, n\right), A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{act}\left(C, A\right) = \operatorname{raw}\left(\operatorname{applyCP}\left(C, \operatorname{toCstar}\left(A\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteTraceDistance.act` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix coordinate equivalence transports the actual completely positive map.

**Definition 1.11 (Actual density distance).**

$$\forall n \in FiniteType, rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right),\; \operatorname{traceDistance}\left(rho, sigma\right) = \frac{\operatorname{traceNorm}\left(\operatorname{raw}\left(rho\right) - \operatorname{raw}\left(sigma\right)\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical density-state values are converted to matrices before taking half the trace norm of their difference.

**Theorem 1.12 (Nonnegative density distance).**

$$\forall n \in FiniteType, rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right),\; 0 \le \operatorname{traceDistance}\left(rho, sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Trace-norm nonnegativity gives the lower endpoint of the density-distance interval.

**Theorem 1.13 (Symmetry).**

$$\forall n \in FiniteType, rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right),\; \operatorname{traceDistance}\left(rho, sigma\right) = \operatorname{traceDistance}\left(sigma, rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing the state difference negates the matrix and preserves its trace norm.

**Theorem 1.14 (Density distance triangle inequality).**

$$\forall n \in FiniteType, rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right), tau \in \operatorname{DensityState}\left(n\right),\; \operatorname{traceDistance}\left(rho, tau\right) \le \operatorname{traceDistance}\left(rho, sigma\right) + \operatorname{traceDistance}\left(sigma, tau\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split the state difference through the intermediate state and apply the trace-norm triangle inequality.

**Theorem 1.15 (All density distances are at most one).**

$$\forall n \in FiniteType, rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right),\; \operatorname{traceDistance}\left(rho, sigma\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each density matrix has trace norm one; the triangle inequality bounds their difference by two.

**Theorem 1.16 (Orthogonal positive difference).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right), B \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{PosSemidef}\left(A\right) \Rightarrow \left(\operatorname{PosSemidef}\left(B\right) \Rightarrow \left(A \cdot B = 0 \Rightarrow \operatorname{traceNorm}\left(A - B\right) = \operatorname{re}\left(\operatorname{trace}\left(A\right)\right) + \operatorname{re}\left(\operatorname{trace}\left(B\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_sub_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive semidefinite complex matrices A and B with A B zero, A plus B is the positive square root of the Gram matrix of A minus B. The trace norm is therefore the sum of their real traces.

**Theorem 1.17 (Hermitian Jordan mass).**

$$\forall n \in FiniteType, A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{Matrix.IsHermitian}(A) \Rightarrow \operatorname{traceNorm}\left(A\right) = \operatorname{re}\left(\operatorname{trace}\left(\operatorname{posPart}\left(A\right)\right)\right) + \operatorname{re}\left(\operatorname{trace}\left(\operatorname{negPart}\left(A\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.trace_norm_jordan_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Hermitian matrix A, its trace norm equals the sum of the real traces of its positive and negative Jordan parts.

**Theorem 1.18 (Every CPTP channel contracts trace distance).**

$$\forall n \in FiniteType, C \in \operatorname{QuantumChannel}\left(n, n\right), rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right),\; \operatorname{traceDistance}\left(\operatorname{mapState}\left(C, rho\right), \operatorname{mapState}\left(C, sigma\right)\right) \le \operatorname{traceDistance}\left(rho, sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split the Hermitian state difference into positive and negative parts. Positivity and trace preservation preserve their trace-norm masses, whose sum is the original trace norm.

The trace-norm proofs and their necessary SVD, orthonormal extension, and unitary row-sum dependencies retain Alex Meiburg's Physlib source at revision 6a09b2d1761a0d4430083045a247eb121d8da260. The Lean owner retains its copyright and full Apache 2.0 license. Retention ends when equivalent declarations are available in this repository's own pinned Mathlib.

Contraction follows from the actual Hermitian Jordan positive and negative parts, their trace-norm mass identity, complete positivity, and trace preservation. It assumes neither a contractivity field nor a Kraus representation of the recovery. The finite-record recovery-error theorem consumes these laws; no computational recovery algorithm is asserted.

For the signed-time prediction application in original Theorem 3.3, let d,e be at least two, H any Hermitian matrix on the joint space, and rho any positive semidefinite trace-one joint state. The partial trace is unnormalized and the trace norm here is unhalved. Set h0=Re Tr(H)/(de), HA=Tr_B(H)/e-h0 I, HB=Tr_A(H)/d, H0=HA tensor I+I tensor HB, and V=H-H0. The same-H residual is R_ab=(id-E_A)[H,W_ab tensor I], where E_A(X)=Tr_B(X) tensor I/e; delta(H) is the maximum of the Euclidean operator norms of these residuals.

A positive matrix R satisfies Re Tr(A R A*) <= ||A||^2 Re Tr(R). Indeed, with S=sqrt(R), the C-star conjugation bound gives S A* A S <= ||A||^2 R. Apply the positive trace map and trace cyclicity. For unitary U,W put D=U-W, M=(U+W)/2, and r=||D||. If r=0 the endpoints agree. Otherwise the positive matrices P_plus=(D+r M)R(D+r M)*/(2r) and P_minus=(D-r M)R(D-r M)*/(2r) have difference U R U*-W R W* and sum D R D*/r+r M R M*. Since ||M||<=1, their total trace is at most 2r Tr(R). Partial trace preserves positivity and the unnormalized trace. The positive trace-norm formula and triangle inequality therefore bound the reduced endpoint difference by 2||U-W|| Tr(R), including singular and correlated R.

Fix any real t and define Z(s)=exp(i t s H0) exp(-i t s H) for 0<=s<=1. The two exponential derivative formulas give Z'(s)=-i t exp(i t s H0) V exp(-i t s H). Both factors are actual unitaries, so ||Z'(s)||<=|t| ||V||. The vector-valued mean-value bound on [0,1], followed by multiplication by exp(-i t H0), yields ||exp(-i t H)-exp(-i t H0)||<=|t| ||V||. The argument includes t<0 and t=0 and uses no commutation assumption on H and H0.

The two Kronecker algebra embeddings preserve the exponential and their images commute, hence exp(-i t H0)=exp(-i t HA) tensor exp(-i t HB). The existing local partial-trace covariance identity applies to every joint matrix, giving Tr_B(exp(-i t H0)rho exp(-i t H0)*)=exp(-i t HA)Tr_B(rho)exp(-i t HA)*. The endpoint estimate and the same-H Weyl reconstruction inequality ||V||<=delta(H) give the bound 2|t|delta(H). Both reduced endpoints are positive trace-one matrices, so their unhalved trace-norm difference is also at most two. Thus the actual reduced-state prediction error is <=min(2,2|t|delta(H)) for every real t and arbitrary joint rho, including noncommuting, singular and correlated states.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.act`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.exists_svd_sqrt_eigenvalues`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.inner_A_mulVec_eq`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.re_trace_eq_trace`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_contract`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_le_one`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_nonneg`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_symm`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_triangle`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_add_le`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_eq_max_re_tr_U`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_neg`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_nonneg`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_of_posSemidef`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_sub_orthogonal`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.trace_norm_jordan_mass`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](FiniteStateChannel.md)
