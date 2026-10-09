---
slug: zhou-bash-guha-gagatsos-2023-transmissivity-beta-prior-refutation
bibkey: zhou2023transmissivity
doi: 10.1103/PhysRevResearch.5.043033
url: https://arxiv.org/abs/2304.05539v1
triage: theorem
motivation_gids:
  - D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.result
---

# In-between-state optimality for transmissivity sensing with a beta prior

## Problem

B. Zhou, B. A. Bash, S. Guha and C. N. Gagatsos, “Bayesian minimum mean
square error for transmissivity sensing”, arXiv:2304.05539v1, Phys. Rev.
Research 5, 043033 (2023), Section VI (p. 6):

> The numerical results indicate that the optimal input states with non-integer
> mean photon number, have the form of Eq. (27), which means that for
> $\bar{n} \in \mathbb{N}$ the optimal states are Fock states.

and Section VII (p. 7):

> We note that for the beta prior PDF, we were not able to prove analytically
> that the Fock states or the in-between states of Eq. (27) states are optimal,
> even though our numerical computations support such conjecture.

The beta prior is eq. (16), $P(\tau)=\tau^{\alpha-1}(1-\tau)^{\beta-1}/\mathcal B(\alpha,\beta)$
with $\alpha,\beta>0$. The verbatim definitions are in
[the literature note](../Library/QuantumStates/zhou2023transmissivity.md).
Issue [#14698](https://github.com/the-omega-institute/trureturing/issues/14698)
preregisters the reading with the parameters free, the witness and the exact
certificates.

## Motivation

The paper gives the first Bayesian treatment of quantum-limited transmissivity
estimation. Its conjectured optimal probe, the adjacent-Fock "in-between" state,
would fix the optimal input for every beta prior at every mean energy; photon
counting on that probe is studied as a practical measurement.

## Gap

The source supports the beta-prior conjecture by sampling 200 random
superpositions of the first five Fock states per energy at two priors,
$\alpha=\beta=1$ and $\alpha=2,\beta=4$, and states that it could not prove it.
The repository refuted the paper's two-point-prior conjecture in
[the two-point dossier](zhou-bash-guha-gagatsos-2023-transmissivity-in-between-probe-refutation.md);
that refutation does not address the beta prior. The literature check in #14698
found no settlement; `not-found-in-searched-scope`.

## Route

Take $\alpha=3$, $\beta=1$ (so $P(\tau)=3\tau^2$) and $\bar n=1/4$. Every phased
in-between state is $\chi_\varphi=\tfrac{\sqrt3}2|0\rangle+\tfrac{e^{i\varphi}}2|1\rangle$;
the probe $\psi=\tfrac{\sqrt{14}}4|0\rangle+\tfrac{\sqrt2}4|2\rangle$ has the same
norm and mean photon number. The moments $\Gamma_k=\int_0^1P(\tau)\tau^k\rho(\tau)\,d\tau$
are integrals of polynomials in $\tau$ and $\sqrt\tau$. The source's error of a Hermitian
$H$ is $\delta_B(H)=\int_0^1P(\tau)\operatorname{tr}[\rho(\tau)(H-\tau)^2]\,d\tau
=\operatorname{tr}(H^2\Gamma_0)-2\operatorname{tr}(H\Gamma_1)+\operatorname{tr}\Gamma_2$, and its
MMSE is the minimum over $H$. For a Hermitian $B$ with $\Gamma_0B+B\Gamma_0=2\Gamma_1$,
$\delta_B(H)-(\operatorname{tr}\Gamma_2-\operatorname{tr}(B\Gamma_1))=\operatorname{tr}((H-B)\Gamma_0(H-B))\ge0$,
with equality at $H=B$. The certificates

$$B_\chi=\begin{pmatrix}216/305&7\sqrt3/183\\7\sqrt3/183&204/305\end{pmatrix}\ (\text{phase-conjugated for }\chi_\varphi),\qquad
B_\psi=\begin{pmatrix}8/11&0&2\sqrt7/77\\0&2/3&0\\2\sqrt7/77&0&20/33\end{pmatrix}$$

give MMSE $167/4575$ for every $\chi_\varphi$ and $2/55$ for $\psi$; the gap is
$7/50325>0$.

## Falsifier

The universal claim is false if one admissible prior and one normalized
competitor at a positive mean energy strictly beat every in-between phase; the
witness above is such a pair. A comparison with one phase, or with photon
counting alone, would not refute the claim.

## Evidence

`D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.lean` defines
`betaDensity`, `momentBeta`, `deltaB` (eq. (2)), `MMSE` (its infimum over Hermitian
operators) and `claim`, proves `deltaB_eq_moments` and `result : ¬ claim`, and reuses
the frozen `meanPhoton`, `outputState` and `inBetween` and the public lemmas
`source_coefficient` and `sourceKraus` of `TransmissivityTwoPointProbeRefutation`,
which this delivery extracts there from local proofs (with `sqrt_power`). The axiom closure of `result` is exactly `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry` or `native_decide`.
The module statement is `sha256:c5a2b30055299db2dc98fdfcc60c13cee5ba7417fe549d2af6cd98e105799f13`; `result` is
`sha256:5fa291fa964c3f4a20d87b08ee8bfa0897b4ae3fa65e8b3104e8e65b2e8b4610` and `claim` is
`sha256:b3e46651536791b6959426a53c968292e3b78f851b92fcc22534ca6edf08098c`. The Freeze event is
`sha256:cc032cc065a64fa248e2b57b52b063239b9a1333d6bf154d6694814ed14461ee`; its project-level prerequisite is the
re-pinned node `sha256:5f016c1168ccdd32fa689bddf160653279b2afbd621505c835d5950cad1e9750` of
`TransmissivityTwoPointProbeRefutation`.

## Triage

Tier 1: a conjecture of a 2023 paper, retained in its journal version,
preregistered in #14698 before any Lean. `theorem`; resolution `refuted`.
`result` and `deltaB_eq_moments` are bind-only (exact Gamma values and interval
integrals, linearity of trace and integral, matrix normalization and square
completion); admission basis
`open-problem-resolution`. Utility `kind=certified-instance; basis=refutes`.
There is no digestion atom.

### What the refutation shows

- **Proved by `result`:** at $\alpha=3,\beta=1$, $\bar n=1/4$, the vacuum–two-photon
  probe $\psi$ has strictly smaller MMSE than every phase of the
  adjacent vacuum–one-photon state, at the same mean energy. Adjacent
  photon-number support is therefore not sufficient for optimality under every
  beta prior.
- **Computed, not formalized (exact rational arithmetic, #14698):** the same
  comparison fails for the in-between state also at $\alpha=3,\beta=1$,
  $\bar n=1/8$ (gap $199/1554300$) and at the interior prior $\alpha=6,\beta=3$,
  $\bar n=1/4$ (gap $46510177/2452113546300$). That prior vanishes at both
  endpoints and has $\alpha,\beta>2$, so the failure does not depend on a prior that
  stays positive at $\tau=1$, as $3\tau^2$ does. At the source's priors $\alpha=\beta=1$ and
  $\alpha=2,\beta=4$, $\bar n=1/4$, the same $\psi$ is worse than the in-between
  state, consistent with the source's figure.
- **Computed, not formalized (floating-point scan over the first five Fock
  states):** the in-between state was the best sampled probe at the source's two
  priors for $\bar n\in\{1/8,1/4,1/2,3/4,3/2\}$, and was beaten at
  $\alpha=3,\beta=1$ for $\bar n\in\{1/8,1/4\}$, where the best sampled probe at
  $\bar n=1/4$ was $\tfrac{\sqrt{15}}4|0\rangle+\tfrac14|4\rangle$. Priors
  concentrated near $\tau=1$ favor spreading a small energy budget onto a
  higher Fock component.
- **Open:** the region of $(\alpha,\beta,\bar n)$ in which an in-between state is
  optimal, the optimal probe where it is not, and the source's integer-energy
  statement that Fock states are optimal for the beta prior (its Fock-state MMSE,
  eq. (39), is not challenged here).
- **Source scope:** conclusions that select the in-between probe by the refuted
  universal claim lose that justification for priors such as $\alpha=3,\beta=1$;
  the fixed-probe risks and photon-counting results of the paper are unaffected.

## ASSUMED-UNVERIFIED

The Lean `MMSE` minimizes $\delta_B$ over Hermitian operators on the span of the
output, $\operatorname{span}\{|0\rangle,\dots,|N\rangle\}$, while the source's $\hat H$
acts on the whole Fock space. With $P$ the projection onto the span and $\rho=P\rho P$,
$\operatorname{tr}[\rho(H-\tau)^2]=\operatorname{tr}[\rho P(H-\tau)^2P]\ge
\operatorname{tr}[\rho(PHP-\tau)^2]$, so the two minima agree; this compression step is
not kernel-checked. The literature check in #14698 is bounded and does not establish
worldwide novelty or priority.
