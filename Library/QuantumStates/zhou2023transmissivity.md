---
bibkey: zhou2023transmissivity
authors: B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos
year: 2023
title: "Bayesian minimum mean square error for transmissivity sensing"
doi: 10.1103/PhysRevResearch.5.043033
url: https://arxiv.org/abs/2304.05539v1
claim: "Section V conjecture: in-between states, up to phase, minimize the two-point-prior MMSE at real mean photon number. Sections VI-VII conjecture: for the beta prior PDF the in-between states (Fock states at integer mean photon number) are optimal."
strata_touched:
  - D5/S3/Estimation/TransmissivityTwoPointProbeRefutation
  - D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation
license: citation-only
triage: anchor
---

# Bayesian transmissivity sensing with a two-point prior

Section V, arXiv v1 PDF p. 4:

> For the two-point prior PDF (15), we verify that for integer n̄ the optimal state is the Fock state with the same photon number. For real n̄, our numerical results support the conjecture that the optimal state has the form of the state (27), up to a phase, i.e., |Φ′ₙ̄⟩ = e^{iφn̂}|Φₙ̄⟩.

The two-point prior is $P(\tau)=q\delta(\tau-\tau_0)+(1-q)\delta(\tau-\tau_1)$,
with $q,\tau_0,\tau_1\in[0,1]$. Pure inputs are
$|\psi\rangle=\sum_{n=0}^N d_n|n\rangle$,
$\sum_n|d_n|^2=1$, and $\sum_n n|d_n|^2=\bar n$ (30)–(32), p. 4.
The pure-loss Kraus operators act as

$$K_l|n\rangle=\sqrt{\binom nl\tau^{n-l}(1-\tau)^l}|n-l\rangle,$$

with zero action for $l>n$. The output is
$\rho(\tau)=\sum_l K_l|\psi\rangle\langle\psi|K_l^\dagger$.
The moment matrices are
$\Gamma_k=q\tau_0^k\rho(\tau_0)+(1-q)\tau_1^k\rho(\tau_1)$.
A finite POVM consists of positive semidefinite effects summing to the identity;
with real estimates $x_j$, its Bayesian risk is

$$\sum_j\operatorname{Re}\operatorname{tr}\!\left(E_j
(x_j^2\Gamma_0-2x_j\Gamma_1+\Gamma_2)\right).$$

The MMSE is the infimum over measurements and estimates. Compression to the finite
output Fock span preserves measurement statistics. The spectral measurement of a
Hermitian solution of $\Gamma_0 B+B\Gamma_0=2\Gamma_1$ attains
$\operatorname{Re}\operatorname{tr}(\Gamma_2-B\Gamma_1)$, while square completion
bounds every finite measurement risk below by that value.

Section V, p. 4:

> For this case, we provide numerical evidence that the optimal state has the form,

Equations (27)–(29) specify

$$|\Phi_{\bar n}\rangle=|a(\bar n)||\lceil\bar n\rceil-1\rangle
+|c(\bar n)||\lceil\bar n\rceil\rangle,\qquad
|c(\bar n)|=\sqrt{1-\lceil\bar n\rceil+\bar n},\qquad
|a(\bar n)|=\sqrt{1-|c(\bar n)|^2}.$$

> We refer to the state of Eq. (27) as in-between state as it is a superposition of the two nearest Fock states for a given n̄ and it reverts to a Fock state when n̄ is an integer.

Equation (33) applies $e^{i\phi\hat n}$ to this state. The Lean encoding quantifies
positive real $\bar n$, all finite Fock cutoffs and all Euclidean-normalized inputs
at that mean energy. `WithLp.toLp 2` supplies the Hilbert norm; the default function
norm would instead be a sup norm. The existing `amplitudeKraus l (1-τ)` implements
$K_l$ with the square root factored into square roots and natural powers. For
$\tau\in[0,1]$,
$\sqrt{\binom nl\tau^{n-l}(1-\tau)^l}=\sqrt{\binom nl}\,(\sqrt\tau)^{n-l}(\sqrt{1-\tau})^l$.
The equality follows from multiplicativity of the real square root on
nonnegative factors and is checked locally where the proof computes outputs.

For $\bar n=1/2$, $q=1/2$, $\tau_0=4/9$, $\tau_1=1$, all phased in-between states
have finite-POVM MMSE $1625/23976$. The normalized competitor
$(\sqrt3/2)|0\rangle+(1/2)|2\rangle$ has the same mean energy and finite-POVM MMSE
$110575/1674432$. The gap is $107725/61953984>0$.
The identification with arbitrary-outcome MMSE is ASSUMED-UNVERIFIED;
the kernel-checked comparison optimizes over finite POVMs.
The Hermitian Sylvester certificates are

$$B_\chi=\frac1{1332}\begin{pmatrix}787&145\\145&937\end{pmatrix},\qquad
B_\psi=\frac1{93024}\begin{pmatrix}62971&0&4293\sqrt3\\0&41344&0\\4293\sqrt3&0&68965\end{pmatrix}.$$

Phase conjugation gives the certificate for every $\chi_\phi$.
The refutation does not assert global optimality of the competitor and does not
settle the beta-prior conjecture in Section VI. The integer-energy result and the
phase-invariance argument are separate from the refuted non-integer-energy claim.

## Beta prior (Sections VI and VII)

The beta prior, eq. (16) (`eq:betaPrior`, arXiv v1 p. 3):

> $P(\tau)=\frac{\tau^{\alpha-1}(1-\tau)^{\beta-1}}{\mathcal{B}(\alpha,\beta)}$, where $\mathcal{B}(\alpha,\beta)=\Gamma(\alpha)\Gamma(\beta)/\Gamma(\alpha+\beta)$, $\Gamma(.)$ is the gamma function, and the values of $\alpha>0$, $\beta>0$ cover a great variety of PDF's behavior.

Section VI ("beta distribution as prior PDF", p. 6), eq. (39) and the following paragraph:

> $\delta=\frac{\alpha \beta}{(\alpha+\beta) (\alpha+\beta+1) (\alpha+\beta+\bar{n})}$. For non-integer mean photon number and non-Fock states, we compute the MSE numerically using the same methods as in Section V. The numerical results indicate that the optimal input states with non-integer mean photon number, have the form of Eq. (27), which means that for $\bar{n} \in \mathbb{N}$ the optimal states are Fock states.

The figure of Section VI (`fig_beta_MMSE`, p. 6) uses $\alpha=\beta=1$ and $\alpha=2,\beta=4$, with 200 random superpositions of the first five Fock states for each $\bar n$. Section VII (p. 7):

> We note that for the beta prior PDF, we were not able to prove analytically that the Fock states or the in-between states of Eq. (27) states are optimal, even though our numerical computations support such conjecture.

The MMSE of the source (Section I, eq. (2) and the following lines, p. 2):

> $\delta_B = \int dx P(x) \text{tr}\left[\hat{\rho}(x)(\hat{H}-x\hat{I})^2\right]$ is the Bayesian mean square error for a measurement given by the eigenvectors of the Hermitian operator $\hat{H}$ on the final state $\hat{\rho}(x)$ … We work with the minimum mean square error (MMSE) where the minimization is performed over all possible protective measurements, i.e., all possible Hermitian operators $\hat{H}$ of Eq. (2), $\delta \equiv \underset{\hat{H}}{\text{min}}\ \delta_B$.

Personick's formulas (12)–(14) evaluate it as $\delta=\operatorname{tr}\Gamma_2-\operatorname{tr}(B\Gamma_1)$ with $\Gamma_k=\int_0^1P(\tau)\tau^k\rho(\tau)\,d\tau$ and $B=2\int_0^\infty e^{-z\Gamma_0}\Gamma_1e^{-z\Gamma_0}\,dz$, the solution of $\Gamma_0B+B\Gamma_0=2\Gamma_1$.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevResearch.5.043033
- URL: https://arxiv.org/abs/2304.05539v1
- PDF: https://arxiv.org/pdf/2304.05539v1 (moment operators p. 3; conjecture p. 4).
- Source: `main.tex`, `eq:betaPrior` (lines 223–227), Section `sec:beta` (lines 371–386) and the discussion paragraph (line 430).
