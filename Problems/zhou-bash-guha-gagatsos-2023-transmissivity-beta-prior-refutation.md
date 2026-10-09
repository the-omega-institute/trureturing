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
are integrals of polynomials in $\tau$ and $\sqrt\tau$. For a Hermitian $B$ with
$\Gamma_0B+B\Gamma_0=2\Gamma_1$, square completion bounds every finite-POVM risk
below by $\operatorname{Re}\operatorname{tr}(\Gamma_2-B\Gamma_1)$, and the
spectral measurement of $B$ with its eigenvalues as estimates attains it. The
certificates

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
`betaDensity`, `momentBeta`, `bayesianRiskBeta`, `MMSEBeta` and `claim`, and proves
`result : ¬ claim`, reusing the frozen `meanPhoton`, `outputState`, `finitePOVM`
and `inBetween` and the public lemmas `source_coefficient`, `sourceKraus`,
`risk_lower_bound` and `spectral_attainment` of
`TransmissivityTwoPointProbeRefutation`, which this delivery extracts there from
local proofs. The axiom closure of `result` is exactly `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry` or `native_decide`.
The module statement is `sha256:f849dd5606fb9b962c207be6593174ddb7d8ca965309b8af5b94b11f410e234f`; `result` is
`sha256:5fa291fa964c3f4a20d87b08ee8bfa0897b4ae3fa65e8b3104e8e65b2e8b4610` and `claim` is
`sha256:11494dc170ad181d6001f91aca995ce21f95d1a8d11bf7801deebdd14101b0f3`. The Freeze event is
`sha256:f34394d73c0c1e948b030678fd6ffc7dad7d273de967dccaecf8e35eb33db14e`; its project-level prerequisite is the
re-pinned node `sha256:23c939c5f9cc97e192a944a078a320eee9ddf6178bfa840d0f7cf2eebb012a7f` of
`TransmissivityTwoPointProbeRefutation`.

## Triage

Tier 1: a conjecture of a 2023 paper, retained in its journal version,
preregistered in #14698 before any Lean. `theorem`; resolution `refuted`.
`result` is bind-only (exact Gamma values and interval integrals, matrix
normalization and the extracted measurement lemmas); admission basis
`open-problem-resolution`. Utility `kind=certified-instance; basis=refutes`.
There is no digestion atom.

### What the refutation shows

- **Proved by `result`:** at $\alpha=3,\beta=1$, $\bar n=1/4$, the vacuum–two-photon
  probe $\psi$ has strictly smaller finite-POVM MMSE than every phase of the
  adjacent vacuum–one-photon state, at the same mean energy. Adjacent
  photon-number support is therefore not sufficient for optimality under every
  beta prior.
- **Computed, not formalized (exact rational arithmetic, #14698):** the same
  comparison fails for the in-between state also at $\alpha=3,\beta=1$,
  $\bar n=1/8$ (gap $199/1554300$) and at the interior prior $\alpha=6,\beta=3$,
  $\bar n=1/4$ (gap $46510177/2452113546300$), so the failure does not rely on a
  prior with a boundary singularity. At the source's priors $\alpha=\beta=1$ and
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

The equality between the finite-POVM MMSE and the source's MMSE over arbitrary
measurements rests on the compression argument recorded in the two-point
dossier and is not kernel-checked. The literature check in #14698 is bounded
and does not establish worldwide novelty or priority.
