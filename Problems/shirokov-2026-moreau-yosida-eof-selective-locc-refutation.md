---
slug: shirokov-2026-moreau-yosida-eof-selective-locc-refutation
bibkey: shirokov2026moreauyosidaeof
doi: null
url: https://arxiv.org/abs/2609.30246v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.result
---

# Selective LOCC can increase Shirokov's Moreau-Yosida entanglement of formation

## Problem

M. E. Shirokov, *The Moreau-Yosida approximation of the EoF: basic properties
and accuracy estimates*, arXiv:2609.30246v1, Section 7, p. 20, asks:

> Open question: can the function $E^{\lambda}_F$ increase under selective LOCC-operations?

The conjectural sentence is:

> So, we may conjecture, at the moment, that the function $E^{\lambda}_F$ does not increase under selective LOCC-operations as well.

Issue [#11557](https://github.com/the-omega-institute/trureturing/issues/11557)
preregisters the source, quantified statement, Tier 1 classification and literature
check. The selective inequality is the probability-weighted average of normalized
terminal values being at most the input value, for every positive parameter and
bipartite state. A finite-dimensional one-round local projective measurement is
already sufficient to refute that universal claim.

## Motivation

Equation (1), (EF-d), takes the infimum of average marginal entropy over **all**
finite pure-state ensembles, with no bound on ensemble size. Entropy uses natural
logarithms. Equation (13), (EFA), defines

$$
E_F^\lambda(\rho)=\inf_{\sigma\in\mathfrak S(\mathcal H_{AB})}
\left(E_F(\sigma)+\frac{\|\rho-\sigma\|_1}{2\lambda}\right).
$$

The trace-norm penalty is unsquared, as explicitly required by the source footnote.
The infimum ranges over every density state on the same ambient bipartite space.

## Gap

arXiv lists v1 and v2. Section 7 of
[v2](https://arxiv.org/html/2609.30246v2) retains the same selective-monotonicity
conjecture and states that no general rigorous proof or counterexample was found.
The finite convex roof and unsquared penalty remain equations (1) and (14).
INSPIRE record 3207115 reports citation count 0 at the metadata reading
2026-10-01 06:00 UTC. The bounded Semantic Scholar and MathDB searches in #11557
are search-seat-reported and found no indexed settlement. Related sources
arXiv:2608.27363 and arXiv:2609.12667 did not provide this settlement in that
search. Not-found-in-searched-scope is not a worldwide priority assertion.
The original v1 TeX and current v2 text independently state the conjecture and
the definitions used here.

Closest prior art: L.-F. Qiao, J. Gao, A. Streltsov, S. Rana, R.-J. Ren, Z.-Q. Jiao,
C.-Q. Hu, X.-Y. Xu, C.-Y. Wang, H. Tang, A.-L. Yang, Z.-H. Ma, M. Lewenstein and
X.-M. Jin, *Activation of entanglement from quantum coherence and superposition*,
Phys. Rev. A 98, 052351 (2018), doi 10.1103/PhysRevA.98.052351,
[arXiv:1710.04447v2](https://arxiv.org/abs/1710.04447v2), Theorem 3 ("Trace norm
entanglement is not a strong entanglement monotone") and Appendix B. Their witness
mixes a rank-two and a rank-three maximally entangled block on a five-dimensional
local space, and Alice's two-outcome block measurement raises the average of
$E_t(\rho)=\min_{\sigma\ \mathrm{separable}}\|\rho-\sigma\|_1$ for $0.4<p<1$. That
paper does not treat $E_F^\lambda$, and Shirokov's v2 still lists the selective
question as open. The witness used here has the same block pattern.

## Route

On $\mathbb C^5\otimes\mathbb C^3$, set
$v_2=e_{00}+e_{11}$, $v_3=e_{20}+e_{31}+e_{42}$,
$\Phi_2=v_2v_2^*/2$, $\Phi_3=v_3v_3^*/3$ and
$\omega=(\Phi_2+\Phi_3)/2$. At $\lambda=7/2$, Alice measures
$\operatorname{diag}(1,1,0,0,0)$ and its complement. Both branches have
probability $1/2$; their normalized outputs are $\Phi_2$ and $\Phi_3$.

For every normalized ambient pure coefficient matrix, the proof bounds entropy
below by $1-\operatorname{Tr}((MM^*)^2)$ and relates this quantity to the squared
absolute $2\times2$ minors. Pair and triple norm estimates give affine entropy
bounds with slope $3/10$ and fidelity offsets $11/20$ and $2/5$. Nonnegativity
allows slope $2/7$. Linearity extends these inequalities to every finite ensemble;
the unitary reflection $2P-I$ supplies the fidelity-to-trace-norm lower bound.
Consequently the output envelope values are at least $9/70$ and $6/35$.

The product-state ensemble of
$\sigma=(|00\rangle\langle00|+|11\rangle\langle11|)/2$ has zero cost,
and $\|\omega-\sigma\|_1\le1$. Thus the input envelope is at most $1/7$,
while the average output is at least $3/20$.

## Falsifier

Changing the convex roof to a restricted ensemble, squaring the penalty, or
omitting the exact Kraus branch equation changes the source claim. The proof
keeps the complete finite convex roof, the unsquared norm, positive dimensions
and parameter, normalized states, and the probability-weighted selective
inequality. The finite-round fixed-space protocol class contains the exhibited
one-round operation; larger source LOCC classes contain that operation too.

## Evidence

The canonical source is
`D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.lean`.
Its sole public theorem is `result : ¬ claim`. The definitions use the canonical
`D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Fin a × Fin b)`
carrier; `CStarMatrix.ofMatrix.symm` supplies the joint Matrix used by the
existing trace and positivity API. They specify complete finite ensembles, the
formation function, the envelope and local instruments. The formal cost is

$$
\operatorname{cost}(e)=\sum_{i\in\operatorname{Fin}(N)} e.p_i\,
S\!\left(\operatorname{marginalRight}
\left(\operatorname{pureDensityState}
\left((a,b)\mapsto(e.\psi_i)_{ab}\right)\right)\right).
$$

Here `pureDensityState` is the frozen constructor from
`EnergyEigenstateStationarity`, built from `rankOneDensity`; its unit-norm proof
comes from the `Pure` property `mass = 1`. `marginalRight` is the frozen density-state partial
trace retaining Alice, and $S$ is the frozen `vonNeumannEntropy`,
$-\operatorname{Re}\operatorname{Tr}(\rho\log\rho)$. Inside `result`,
`InputInformationBalance.entropy_eq_sum` identifies this literal reduced-state
entropy with the Shannon entropy of the eigenvalues of $MM^*$.
`E_F` and `E_F_my` have carrier $[0,+\infty]$; `ENNReal.ofReal` embeds their
nonnegative real cost and, for $\lambda>0$, penalty expressions. The proof uses
the frozen `CompositeMatrix`, `rankOneDensity`, `pureDensityState`,
`marginalRight`, `vonNeumannEntropy`, `entropy_eq_sum`, `support`,
`shannonEntropy` and matrix trace-norm API directly. All estimates
and witness equations are proved inside `result`; there is no `sorry`,
`native_decide` or new axiom. The Scribe resolution is `Refuted`.

## Triage

Tier 1 external named open problem, preregistered in #11557. The settling
result has `proof_shape: bind-only`, `escape_witness: none`, and
`admission_basis: open-problem-resolution`. The utility is a certified instance
with typed `claim` and `result`, basis `refutes`. There is no digestion atom.

Information-escape registration is paused under CLAUDE.md §3.9
「信息逃逸登记暂缓」; no `Reg` source or `declared_validated` record is part of
this delivery.

### What the settlement shows

- **Proved in this module**, `result`: the source's selective-monotonicity
  conjecture fails for a two-outcome local projective measurement on a
  $5\times3$ system at $\lambda=7/2$. Its proof establishes input $\le1/7$,
  output average $\ge3/20$, and a strict gap of at least $1/140$.
- **Proved in this module**, within `result`: a single separable approximant
  bounds the mixed input cheaply, while affine fidelity bounds force a larger
  probability-weighted cost after resolving the two orthogonal local blocks.
  This mechanism does not require a restricted convex roof or a numerical
  optimizer. The Schmidt-rank-two and Schmidt-rank-three outputs share the
  same ambient state space.
- **Proved in this module**, from the branch equations within `result` and
  the definition of `omega`: forgetting the outcome record of this particular
  measurement returns `omega`, since its unnormalized branches are
  `(1/2) Phi_2` and `(1/2) Phi_3`. The surviving nonselective statement for
  this witness is equality of the input and the averaged output state.
- **Open in this module; source-attested**, Corollary 1: nonselective LOCC-monotonicity is a
  distinct proved property in the paper. This refutation does not invalidate
  its nonselective argument, convexity or accuracy estimates; those general
  statements are not independently kernel-certified by this delivery.
- **Open formal bridge / source consequence**: Section 7's proposed universal
  flag equality (FL) cannot establish the refuted selective conjecture with
  its stated full scope. No explicit flag-state counterexample or formal
  proof of the paper's sufficiency criterion is delivered here. The proposed
  classification as a true selective entanglement monotone has no such
  universal justification.
- **Derived here, not kernel-checked**: on a fixed finite-dimensional space,
  $2\lambda E_F^\lambda(\rho)=\inf_\sigma\bigl(2\lambda E_F(\sigma)+\|\rho-\sigma\|_1\bigr)$
  is nondecreasing in $\lambda$ and bounded by $E_t(\rho)$, because separable
  $\sigma$ have $E_F(\sigma)=0$. The state space is compact and $E_F$ is
  continuous, so the infimum is attained at some $\sigma_\lambda$, and
  $2\lambda E_F(\sigma_\lambda)\le E_t(\rho)$. Every limit point of
  $(\sigma_\lambda)$ as $\lambda\to\infty$ is therefore separable; since
  $2\lambda E_F^\lambda(\rho)\ge\|\rho-\sigma_\lambda\|_1$, this gives
  $2\lambda E_F^\lambda(\rho)\to E_t(\rho)$. Hence the strict violation of Qiao et al. (2018) for $E_t$
  transfers to $E_F^\lambda$ for all sufficiently large $\lambda$; the conjecture's
  failure at large $\lambda$ already follows from that example. This module adds a
  kernel-checked violation at the explicit finite parameter $\lambda=7/2$ with the
  explicit gap $1/140$.
- **Open**: whether a violation exists for every $\lambda>0$. As $\lambda\to0$,
  $E_F^\lambda\to E_F$, and $E_F$ itself does not increase on average under
  selective LOCC, so small $\lambda$ is the remaining case.
- **Open**: the smallest dimensions admitting a violation, the full parameter
  range of this witness, and sufficient hypotheses restoring selective
  monotonicity. No general small-parameter or equal-Schmidt-rank conclusion
  is claimed. These are separate candidates, not companion theorems.

## ASSUMED-UNVERIFIED

The prior search-seat literature readings are not an exhaustive literature
check. The large-$\lambda$ transfer from Qiao et al. stated under Triage is a
written argument, not a kernel-checked statement. The infinite-dimensional convex roof, infinite-round protocols,
flag-equivalence bridge and neighboring parameter/dimension questions are not
formalized by this module. The larger LOCC interpretation uses the ordinary
inclusion of this explicit local projective measurement, rather than a Lean
formalization of every source LOCC class.
