# Gibbs Variational Identity

## Abstract

The normalized matrix exponential gives an exact entropy decomposition.

Matrices are complex and indexed by an arbitrary finite nonempty type n. H is Hermitian. DensityState means a positive semidefinite matrix with complex trace one. ReTr is the real part of the matrix trace. partitionFunction(H) is ReTr(exp(H)) and is strictly positive; gibbsState(H) is its inverse scalar times exp(H), a positive definite density matrix. Every logarithm is natural and the matrix logarithm is Mathlib's spectral continuous functional calculus.

For any Hermitian Hamiltonians A and B and inverse temperature beta > 0, put V = A - B and c equal to the Euclidean induced operator norm of V. Here exp is the full complex matrix exponential. Write Z(A) = ReTr(exp(-beta A)), f(A) = -beta^(-1) log Z(A), and gamma(A) = Z(A)^(-1) exp(-beta A), and likewise for B. For every canonical positive semidefinite density rho with trace one, the three comparisons are |ReTr(rho V)| <= c, |f(A)-f(B)| <= c, and |beta^(-1) D(rho || gamma(A))-beta^(-1) D(rho || gamma(B))| <= 2c. These are applications of existing results, with no commutation or invertibility assumption on rho: it can be singular and can fail to commute with either Hamiltonian.

The signed Hermitian order envelope -c I <= V <= c I and positive trace pairing with rho give the expectation estimate. The existing abs_eigenvalue_sub_eigenvalue_le theorem, applied to the same Euclidean operators, bounds the paired eigenvalues by c. The re_trace_cfc spectral trace formula and the continuous-functional-calculus exponential then give exp(-beta c) Z(B) <= Z(A) <= exp(beta c) Z(B). Positive partition functions and logarithm monotonicity yield the free-energy estimate. Subtracting gibbs_variational_identity at the same rho gives exactly beta^(-1)(D(rho || gamma(A))-D(rho || gamma(B))) = ReTr(rho V) - (f(A)-f(B)); the triangle inequality gives 2c. The CFC exponential agrees with the full matrix exponential, so Z(A) and Z(B) are strictly positive and the normalized matrices are exactly the canonical Gibbs densities obtained through fromLegacyDensityState. Each is positive definite. Thus SupportContained rho gamma holds for both references, and the extended relative entropy equals the finiteTraceLogRelativeEntropy branch used for D. This justifies the finite trace-log entropy even for singular rho. The trace-exponential comparison is also discussed by Alhambra, PRX Quantum 4, 040201 (2023), Section III.D, equations (53)-(54), doi:10.1103/PRXQuantum.4.040201.

For a Hermitian H on Fin d x Fin e with d,e >= 2, define h0 = ReTr(H)/(de), HA = e^(-1) TrB(H) - h0 I_d, and HB = d^(-1) TrA(H), where TrB is partialTraceRight and TrA is partialTraceLeft of this same H. Only HA is centered. Partial traces preserve Hermiticity, so H0 = HA tensor I_e + I_d tensor HB and V = H - H0 are Hermitian. The comparisons apply with A = H, B = H0 and the same arbitrary joint density rho and every beta > 0, with c the Euclidean operator norm of H - H0. These finite-matrix estimates require no physical realization assumptions. A physical interpretation must supply its own Hamiltonian and state hypotheses. Replacing c by a Weyl residual delta(H) additionally requires the bound c <= delta(H). Tensor factorization of the Gibbs state, dynamical prediction, and recovery estimates require their own identities.

**Lemma 1.1 (Logarithm of the Gibbs state).**

$$\forall n \in FiniteNonemptyType, H \in \operatorname{HermitianMatrix}\left(n\right),\; \operatorname{log}\left(\operatorname{gibbsState}\left(H\right)\right) = H - \operatorname{log}\left(\operatorname{partitionFunction}\left(H\right)\right) \cdot I$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.log_gibbs_state` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The logarithm of a positive scalar multiple separates into a scalar logarithm and the matrix logarithm. The logarithm of the exponential of a Hermitian matrix is the original matrix.

**Theorem 1.2 (Gibbs entropy decomposition).**

$$\forall n \in FiniteNonemptyType, H \in \operatorname{HermitianMatrix}\left(n\right), rho \in \operatorname{DensityState}\left(n\right),\; \operatorname{log}\left(\operatorname{partitionFunction}\left(H\right)\right) = \operatorname{ReTr}\left(H \cdot rho\right) + \operatorname{vonNeumannEntropy}\left(rho\right) + \operatorname{quantumRelativeEntropy}\left(rho, \operatorname{gibbsState}\left(H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.gibbs_variational_identity` (`✓ std3`). ∎

*Citation.* John Goold, Marcus Huber, Arnau Riera, Lídia del Rio, Paul Skrzypczyk (2016). *The role of quantum information in thermodynamics — a topical review*. DOI: [10.1088/1751-8113/49/14/143001](https://doi.org/10.1088/1751-8113/49/14/143001).

*Commentary.*

Expanding relative entropy cancels the self-logarithm term against von Neumann entropy. Substitution of the Gibbs logarithm, trace normalization, and cyclicity of the trace give the equality. The density matrix may fail to commute with H.

**Theorem 1.3 (The maximally mixed reference state).**

$$\forall n \in FiniteNonemptyType, rho \in \operatorname{DensityState}\left(n\right),\; \operatorname{vonNeumannEntropy}\left(rho\right) + \operatorname{quantumRelativeEntropy}\left(rho, \operatorname{gibbsState}\left(0\right)\right) = \operatorname{log}\left(\operatorname{card}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.entropy_uniform_identity` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

At H = 0 the partition function is card(n), and gibbs_state_zero identifies the Gibbs matrix with I/card(n). Substitution into the general identity gives entropy plus relative entropy to the maximally mixed state equal to log(card(n)).

## References

- Truth anchor: `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.entropy_uniform_identity`
- Truth anchor: `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.gibbs_variational_identity`
- Truth anchor: `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.log_gibbs_state`
- Dependency: [D5/S3/Quantum/Divergence/VonNeumannEntropyPinching](VonNeumannEntropyPinching.md)
