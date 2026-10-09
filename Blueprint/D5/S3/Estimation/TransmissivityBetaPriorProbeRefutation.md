# In-between states need not be optimal for a beta prior

## Abstract

At mean photon number one quarter and beta parameters alpha=3, beta=1, a vacuum–two-photon probe has strictly smaller Hermitian-measurement Bayesian error than every phased in-between state.

**Definition 1.1 (Beta prior density).**

$$\forall alpha : \mathbb{R}, \forall beta : \mathbb{R}, \forall tau : \mathbb{R}, \operatorname{betaDensity}\left(alpha, beta, tau\right) = \frac{((tau)^{alpha - 1}) \cdot ((1 - tau)^{beta - 1})}{\frac{(\operatorname{Gamma}\left(alpha\right)) \cdot (\operatorname{Gamma}\left(beta\right))}{\operatorname{Gamma}\left(alpha + beta\right)}}$$

*Formalization.* `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.betaDensity` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Section VI: P(tau)=tau^(alpha-1)(1-tau)^(beta-1)/B(alpha,beta), with B(alpha,beta)=Gamma(alpha)Gamma(beta)/Gamma(alpha+beta). Both exponents are real powers, and Gamma is the real gamma function. The prior is used on the interval [0,1]; the definition extends to raw real parameters, while the conjecture assumes alpha and beta positive.

**Definition 1.2 (Beta prior moment matrices).**

$$\forall N : \mathbb{N}, \forall alpha : \mathbb{R}, \forall beta : \mathbb{R}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, \forall k : \mathbb{N}, \forall i : \operatorname{Fin}\left(N + 1\right), \forall j : \operatorname{Fin}\left(N + 1\right), \operatorname{momentBeta}\left(N, alpha, beta, psi, k\right)\left(i, j\right) = \int_{0}^{1} ((\operatorname{ofReal}\left((\operatorname{betaDensity}\left(alpha, beta, tau\right)) \cdot ((tau)^{k})\right)) \cdot (\operatorname{outputState}\left(N, tau, psi\right)\left(i, j\right))) dtau$$

*Formalization.* `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.momentBeta` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Gamma_k is the entrywise interval integral of P(tau) tau^k rho(tau) on [0,1], with the real scalar cast to complex numbers. outputState is the pure-loss Kraus output on the finite Fock span, reused from the two-point formulation. k is a natural exponent.

**Definition 1.3 (Bayesian error of a Hermitian observable).**

$$\forall N : \mathbb{N}, \forall alpha : \mathbb{R}, \forall beta : \mathbb{R}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, \forall H : \operatorname{Matrix}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{Fin}\left(N + 1\right), \mathbb{C}\right), \operatorname{deltaB}\left(N, alpha, beta, psi, H\right) = \int_{0}^{1} ((\operatorname{betaDensity}\left(alpha, beta, tau\right)) \cdot (\operatorname{Re}\left(\operatorname{trace}\left((\operatorname{outputState}\left(N, tau, psi\right)) \cdot ((H - \operatorname{smul}\left(\operatorname{ofReal}\left(tau\right), 1\right))^{2})\right)\right))) dtau$$

*Formalization.* `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.deltaB` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Section I, equation (2): delta_B is the interval integral of P(tau) Re(trace(rho(tau) (H-tau I)^2)). The source measures in the eigenvectors of the Hermitian observable H, with its eigenvalues as estimates. The definition accepts any matrix H on the finite output span; the minimum restricts H to Hermitian matrices.

**Definition 1.4 (Minimum over Hermitian observables).**

$$\forall N : \mathbb{N}, \forall alpha : \mathbb{R}, \forall beta : \mathbb{R}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, \operatorname{MMSE}\left(N, alpha, beta, psi\right) = \operatorname{sInf}\left(\{r : \mathbb{R} \mid \exists H : \operatorname{Matrix}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{Fin}\left(N + 1\right), \mathbb{C}\right), (\operatorname{IsHermitian}\left(H\right)) \land (r = \operatorname{deltaB}\left(N, alpha, beta, psi, H\right))\}\right)$$

*Formalization.* `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.MMSE` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Section I, the line after equation (2): the error is minimized over all Hermitian observables H. The Lean definition takes the real infimum of deltaB over Hermitian matrices on the output span. The certificates used here attain that infimum, giving the source's minimum.

**Theorem 1.5 (Integral error in terms of the prior moments).**

$$\forall N : \mathbb{N}, \forall alpha : \mathbb{R}, \forall beta : \mathbb{R}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, \forall H : \operatorname{Matrix}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{Fin}\left(N + 1\right), \mathbb{C}\right), (\operatorname{ContinuousOn}\left(\operatorname{betaDensity}\left(alpha, beta\right), \operatorname{Icc}\left(0, 1\right)\right)) \Rightarrow (\operatorname{deltaB}\left(N, alpha, beta, psi, H\right) = \operatorname{Re}\left(\operatorname{trace}\left(((H) \cdot (H)) \cdot (\operatorname{momentBeta}\left(N, alpha, beta, psi, 0\right))\right) - (2) \cdot (\operatorname{trace}\left((H) \cdot (\operatorname{momentBeta}\left(N, alpha, beta, psi, 1\right))\right)) + \operatorname{trace}\left(\operatorname{momentBeta}\left(N, alpha, beta, psi, 2\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.deltaB_eq_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the prior density is continuous on [0,1], expanding (H-tau I)^2 and integrating entry by entry gives Re(trace(H H Gamma_0)-2 trace(H Gamma_1)+trace(Gamma_2)). The pure-loss output entries are continuous. Cyclicity of trace places each moment matrix on the right; Hermiticity of H is not needed for this identity.

**Definition 1.6 (Beta-prior in-between optimality conjecture).**

$$claim \Leftrightarrow (\forall alpha : \mathbb{R}, \forall beta : \mathbb{R}, \forall nbar : \mathbb{R}, (0 < alpha) \Rightarrow ((0 < beta) \Rightarrow ((0 < nbar) \Rightarrow (\forall N : \mathbb{N}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, (\operatorname{norm}\left(\operatorname{toLp}\left(2, psi\right)\right) = 1) \Rightarrow ((\operatorname{meanPhoton}\left(N, psi\right) = nbar) \Rightarrow (\exists phi : \mathbb{R}, \operatorname{MMSE}\left(\operatorname{ceilNat}\left(nbar\right), alpha, beta, \operatorname{inBetween}\left(nbar, phi\right)\right) \le \operatorname{MMSE}\left(N, alpha, beta, psi\right)))))))$$

*Formalization.* `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.claim` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Section VI: "The numerical results indicate that the optimal input states with non-integer mean photon number, have the form of Eq. (27), which means that for nbar in N the optimal states are Fock states." Section VII: "We note that for the beta prior PDF, we were not able to prove analytically that the Fock states or the in-between states of Eq. (27) states are optimal, even though our numerical computations support such conjecture." The encoding quantifies over positive alpha, beta and nbar, every finite cutoff N, and normalized pure inputs with mean photon number nbar. Some phase of the in-between state is asserted to have no greater MMSE than each competitor. Each Hermitian observable acts on the corresponding finite output span. The refutation uses alpha=3, beta=1, outside the two parameter pairs sampled in the source's figure.

**Theorem 1.7 (A strictly better nonadjacent probe).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhou-bash-guha-gagatsos-2023-transmissivity-beta-prior-refutation` (refuted) by `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhou-bash-guha-gagatsos-2023-transmissivity-beta-prior-refutation","declaration_gid":"D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take alpha=3, beta=1 and nbar=1/4. The prior density is 3 tau^2. Every in-between phase has MMSE at least 167/4575, while psi=(sqrt(14)/4)|0>+(sqrt(2)/4)|2> has MMSE at most 2/55. The difference is 7/50325>0. Both inputs have Euclidean norm one and mean photon number one quarter. Exact polynomial and square-root integrals give the moment matrices. The phased in-between Hermitian observable has diagonal entries 216/305 and 204/305, and off-diagonal entries 7 sqrt(3) star(z)/183 and 7 sqrt(3) z/183, with z star(z)=1. The competitor observable is [[8/11,0,2 sqrt(7)/77],[0,2/3,0],[2 sqrt(7)/77,0,20/33]]. Each solves Gamma_0 B+B Gamma_0=2 Gamma_1. Positive rank-one plus nonnegative diagonal decompositions establish positivity of Gamma_0. Square completion bounds deltaB for every Hermitian H from below by Re(trace(Gamma_2)-trace(B Gamma_1)); substituting H=B attains the bound. Thus the comparison uses the source's minimum over Hermitian observables. The rational strict inequality contradicts the conjecture; it does not assert global optimality of the competing probe.

## References

- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.MMSE`
- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.betaDensity`
- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.claim`
- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.deltaB`
- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.deltaB_eq_moments`
- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.momentBeta`
- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.result`
- Dependency: [D5/S3/Estimation/TransmissivityTwoPointProbeRefutation](TransmissivityTwoPointProbeRefutation.md)
