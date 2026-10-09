# In-between states need not be optimal for a beta prior

## Abstract

At mean photon number one quarter and beta parameters alpha=3, beta=1, a vacuum–two-photon probe has strictly smaller finite-measurement Bayesian error than every phased in-between state.

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

**Definition 1.3 (Bayesian quadratic risk).**

$$\forall N : \mathbb{N}, \forall m : \mathbb{N}, \forall alpha : \mathbb{R}, \forall beta : \mathbb{R}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, \forall E : \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{Fin}\left(N + 1\right), \mathbb{C}\right), \forall x : \operatorname{Fin}\left(m\right) \to \mathbb{R}, \operatorname{bayesianRiskBeta}\left(N, m, alpha, beta, psi, E, x\right) = \sum_{k : \operatorname{Fin}\left(m\right)} (\operatorname{Re}\left(\operatorname{trace}\left((E\left(k\right)) \cdot (\operatorname{smul}\left(\operatorname{ofReal}\left((x\left(k\right))^{2}\right), \operatorname{momentBeta}\left(N, alpha, beta, psi, 0\right)\right) - \operatorname{smul}\left(\operatorname{ofReal}\left((2) \cdot (x\left(k\right))\right), \operatorname{momentBeta}\left(N, alpha, beta, psi, 1\right)\right) + \operatorname{momentBeta}\left(N, alpha, beta, psi, 2\right))\right)\right))$$

*Formalization.* `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.bayesianRiskBeta` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

For a finite POVM E and real estimates x, the risk is the sum of real parts of traces E_k(x_k^2 Gamma_0-2 x_k Gamma_1+Gamma_2). The estimates are cast to complex scalars before matrix scalar multiplication. finitePOVM requires each effect positive semidefinite and the sum of effects equal to the identity.

**Definition 1.4 (Minimum finite-POVM error).**

$$\forall N : \mathbb{N}, \forall alpha : \mathbb{R}, \forall beta : \mathbb{R}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, \operatorname{MMSEBeta}\left(N, alpha, beta, psi\right) = \operatorname{sInf}\left(\{r : \mathbb{R} \mid \exists m : \mathbb{N}, \exists E : \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{Fin}\left(N + 1\right), \mathbb{C}\right), \exists x : \operatorname{Fin}\left(m\right) \to \mathbb{R}, (\operatorname{finitePOVM}\left(N, m, E\right)) \land (r = \operatorname{bayesianRiskBeta}\left(N, m, alpha, beta, psi, E, x\right))\}\right)$$

*Formalization.* `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.MMSEBeta` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

The real infimum ranges over every natural outcome count, every finite POVM on the output span, and every real estimate vector. ASSUMED-UNVERIFIED: identifying this finite-outcome quantity with the source's optimum over arbitrary measurements requires compression to the finite output span and reduction from arbitrary outcomes to finite outcomes. Those bridges are not kernel-checked here. The lower bound and spectral attainment in this module concern finite POVMs.

**Definition 1.5 (Beta-prior in-between optimality conjecture).**

$$claim \Leftrightarrow (\forall alpha : \mathbb{R}, \forall beta : \mathbb{R}, \forall nbar : \mathbb{R}, (0 < alpha) \Rightarrow ((0 < beta) \Rightarrow ((0 < nbar) \Rightarrow (\forall N : \mathbb{N}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, (\operatorname{norm}\left(\operatorname{toLp}\left(2, psi\right)\right) = 1) \Rightarrow ((\operatorname{meanPhoton}\left(N, psi\right) = nbar) \Rightarrow (\exists phi : \mathbb{R}, \operatorname{MMSEBeta}\left(\operatorname{ceilNat}\left(nbar\right), alpha, beta, \operatorname{inBetween}\left(nbar, phi\right)\right) \le \operatorname{MMSEBeta}\left(N, alpha, beta, psi\right)))))))$$

*Formalization.* `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.claim` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Section VI: "The numerical results indicate that the optimal input states with non-integer mean photon number, have the form of Eq. (27), which means that for nbar in N the optimal states are Fock states." Section VII: "We note that for the beta prior PDF, we were not able to prove analytically that the Fock states or the in-between states of Eq. (27) states are optimal, even though our numerical computations support such conjecture." The encoding quantifies over positive alpha, beta and nbar, every finite cutoff N, and normalized pure inputs with mean photon number nbar. Some phase of the in-between state is asserted to have no greater MMSE than each competitor. The finite-measurement scope is the one specified above. The refutation uses alpha=3, beta=1, outside the two parameter pairs sampled in the source's figure.

**Theorem 1.6 (A strictly better nonadjacent probe).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhou-bash-guha-gagatsos-2023-transmissivity-beta-prior-refutation` (refuted) by `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhou-bash-guha-gagatsos-2023-transmissivity-beta-prior-refutation","declaration_gid":"D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take alpha=3, beta=1 and nbar=1/4. The prior density is 3 tau^2. Every in-between phase has finite-POVM MMSE at least 167/4575, while psi=(sqrt(14)/4)|0>+(sqrt(2)/4)|2> has MMSE at most 2/55. The difference is 7/50325>0. Both inputs have Euclidean norm one and mean photon number one quarter. Exact polynomial and square-root integrals give the moment matrices. The phased in-between Hermitian observable has diagonal entries 216/305 and 204/305, and off-diagonal entries 7 sqrt(3) star(z)/183 and 7 sqrt(3) z/183, with z star(z)=1. The competitor observable is [[8/11,0,2 sqrt(7)/77],[0,2/3,0],[2 sqrt(7)/77,0,20/33]]. Each solves Gamma_0 B+B Gamma_0=2 Gamma_1. Positive rank-one plus nonnegative diagonal decompositions establish positivity of Gamma_0. Square completion bounds every finite POVM risk from below, and the observable's spectral measurement attains the bound. The rational strict inequality contradicts the conjecture; it does not assert global optimality of the competing probe.

## References

- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.MMSEBeta`
- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.bayesianRiskBeta`
- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.betaDensity`
- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.claim`
- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.momentBeta`
- Truth anchor: `D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.result`
- Dependency: [D5/S3/Estimation/TransmissivityTwoPointProbeRefutation](TransmissivityTwoPointProbeRefutation.md)
