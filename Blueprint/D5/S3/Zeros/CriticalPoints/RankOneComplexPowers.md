# The sharp spectral moment inequality

## Abstract

Private rank-one powers and strip interpolation yield the public spectral moment bound and transfer.

**Theorem 1.1 (The reciprocal critical-point moment).**

Lean statement: `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.reciprocal_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.reciprocal_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite family of nonzero complex z_j and every real p, the sum of norm(w)^(−p) over the derivative roots of the reused polynomial P is exactly the p-th norm moment of the characteristic roots of D(I+J), where D has diagonal entries 1/z_j. This directly reuses the multiplicity-preserving reciprocal-root identity.

**Theorem 1.2 (The spectral bound and strict-order rigidity).**

Lean statement: `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.spectral_bound_and_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.spectral_bound_and_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural n and complex s, H(n,s) is I plus ((n+1)^s−1) times J/n, where the scalar power is exp(s log(n+1)). For n>0 these matrices multiply by adding exponents, H(n,0)=I, H(n,1)=I+J, and imaginary powers are unitary. The auxiliary positivePower function uses a real logarithm and agrees with Real.rpow on positive bases and real exponents.

For n>0 and every real p, each column r_j of H(n,p/2), regarded as a complex Euclidean vector, has squared norm ((n+1)^p+n−1)/n. The inner products of distinct columns are ((n+1)^p−1)/n. For p>0 every pairwise inner product is nonzero, including diagonal pairs.

For every natural n, real p and complex diagonal d, the matrix H(n,p/2) diag(d) H(n,p/2) is the sum over j of d_j times r_j r_j*. The columns are those of the same explicit Hermitian power. This expansion connects the interpolation matrix to the unitary rank-one trace estimate.

StripData records an entire complex function with a uniform finite norm bound on the closed vertical strip 0≤Re(z)≤1. The data are closed under finite sums, addition and multiplication. Exponentials exp(a z+b) with real slope a have this property, and the API supplies the boundedness required by the three-lines theorem.

Given n, a complex matrix Q, complex families u,v, real families t,rho and real p, define F(z)=H(n,pz/2) diag(u_j positivePower(t_j,pz)) H(n,pz/2), K(z)=Q diag(conj(v_k) positivePower(rho_k,p(1−z))) Q*, and f(z)=Tr(K(z)F(z)). Each entry is built from explicit scalar exponentials and finite matrix products.

For all supplied finite data, the scalar trace family f has StripData: it is entire and bounded on the closed strip. No positivity, phase normalization, unitary basis or triangularity assumption is needed for this analytic statement.

For n>0, unitary Q, unit phases u and v, positive rho and sum_k rho_k^p=1, the norm of f(iy) is at most one for every real y. The left F matrix is unitary; in the Q basis the absolute diagonal weights sum to one. On the right boundary, K is unitary whenever Q and v have these unitary and phase properties.

For n>0, p>0, positive t_j, unit phases u_j, every real y and every unitary matrix K, the norm of Tr(K H(n,p(1+iy)/2) diag(u_j positivePower(t_j,p(1+iy))) H(n,p(1+iy)/2)) is at most M=((n+1)^p+n−1)/n times sum_j t_j^p. If equality holds, then u_i exp(ipy log t_i)=u_j exp(ipy log t_j) for every i,j. The explicit Hermitian-power columns have equal squared norms and pairwise nonzero inner products.

Let p>0 and let t_j and rho_k be positive. Suppose b_j=u_j t_j, and let mu_k be the diagonal entries of Q* H(n,1/2) diag(b) H(n,1/2) Q. If sum_k conj(v_k) rho_k^(p−1) mu_k=N, then the interpolation trace f(1/p) equals N as a complex number. Trace cyclicity and the identities p(1/p)=1 and p(1−1/p)=p−1 suffice; Q need not be unitary and the conjugated matrix need not be triangular.

For a nonempty finite family of nonzero complex mu_k and p>0, there exist N>0, positive rho_k and unit phases v_k with mu_k=v_k N rho_k, sum_k rho_k^p=1, N^p=sum_k norm(mu_k)^p, and sum_k conj(v_k) rho_k^(p−1) mu_k=N. Thus the same normalized data serve both the left boundary and interpolation center.

If Q is unitary and Q* A Q is upper triangular, the sum of norm-to-p over every characteristic root of A, counted with multiplicity, equals the sum of norm-to-p over the diagonal entries of Q* A Q. The identity holds for every real p.

For n>0 and arbitrary complex diagonal b, define A=H(n,1/2) diag(b) H(n,1/2). Its characteristic polynomial equals that of diag(b)(I+J). If all b_j are nonzero, A is invertible; consequently every diagonal entry in a unitary upper-triangular Schur form is nonzero.

For n>0, nonzero complex b_j and every real p≥1, the sum of norm(mu)^p over characteristic roots of diag(b)(I+J), with multiplicity, is at most ((n+1)^p+n−1)/n times sum_j norm(b_j)^p. For p>1, equality implies b_i=b_j for every i,j. The endpoint uses the unitary rank-one trace bound; strict orders use one fixed Schur basis, scalar three-lines interpolation and propagation of equality to all right boundary phases.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.reciprocal_moment`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.spectral_bound_and_rigidity`
- Dependency: [D5/S3/Zeros/CriticalPoints/RankOneTraceBound](RankOneTraceBound.md)
- Dependency: [D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo](TangZhangOrderMinusTwo.md)
