---
slug: barato-seifert-2015-waiting-time-randomness-skewness-refutation
bibkey: baratoseifert2015skewness
doi: 10.1103/PhysRevLett.115.188103
url: https://arxiv.org/abs/1510.03279v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.result
---

# Skewness at most two does not force randomness at most one in multicyclic enzyme networks

## Problem

A. C. Barato and U. Seifert, *Skewness and Kurtosis in Statistical Kinetics*, Phys. Rev. Lett. 115, 188103 (2015), arXiv:1510.03279v1, ask in `skewkurtstatkinarxiv.tex`, line 358, at the end of the multicyclic discussion:

> It remains as an open question whether this property is true for arbitrary networks that do not consist of a single cycle.

The preceding numerical investigation concerns a four-state network with two product-forming routes and its off-pathway specialization. At lines 350–352 the authors report that constraining the skewness to be at most two prevents the randomness parameter from exceeding one. The question asks whether the superior detection of departures from a single cycle by higher moments extends to arbitrary networks.

The source defines cycle completion at an irreversible product-release transition (Eq. `fullreaction`, lines 110–117). For completion-time moments $t_n$, its definitions at lines 133–149 are
$$
\sigma^2=t_2-t_1^2,\qquad
\mathcal R=\frac{\sigma^2}{t_1^2},\qquad
\mathcal S=\frac{t_3-3t_1\sigma^2-t_1^3}{\sigma^3}.
$$

The source's kurtosis is $\mathcal K=(t_4-4t_3t_1+6\sigma^2t_1^2+3t_1^4)/\sigma^4$ (line 149); it is not used by the settlement.

Issue [#26046](https://github.com/the-omega-institute/trureturing/issues/26046) fixes the implication to be refuted: for every finite network with nonnegative off-diagonal rates, a positive marked rate $p\to r$, every state able to reach $p$, and positive variance, $\mathcal S\le2$ implies $\mathcal R\le1$. Moments use the first-passage matrix definition below. This implication is refuted.

The [literature note](../Library/StatisticalMechanics/baratoseifert2015skewness.md) records the source and its scope.

## Motivation

A completion-time statistic above its unicyclic upper bound provides a signature that the network is more complex than a single cycle. A universal implication $\mathcal S\le2\Rightarrow\mathcal R\le1$ would mean that skewness detects every departure detected by randomness. Its refutation identifies a topology where randomness detects a departure while skewness stays below its proposed unicyclic threshold.

## Gap

Issue #26046 records the bounded literature check before any Lean:

- The arXiv v1 source states the open question explicitly.
- The search author traced OpenCitations and Crossref citation trails and reported reading Ptaszyński, arXiv:1801.03715 and 2204.08421; Wierenga–ten Wolde–Becker, arXiv:1801.05392; Pal–Reuveni–Rahav, arXiv:2103.16578; Wampler–Barato, arXiv:2110.14540; and arXiv:2305.09759, 2407.03629, 2411.19643 and 2506.08877, finding no settlement of this ordering.
- Four subscription-only citing papers could not be read.
- The preregistration records no existing repository dossier, Library note or issue for the source at that check.

`not-found-in-searched-scope`.

## Route

Write $G=\operatorname{cemetery}(k,p,r)$, $A=-G$, $m_0=\mathbf1$, $m_{n+1}=(n+1)A^{-1}m_n$ and $t_n=m_n(r)$, as in `cemetery` and `moment`. The diagonal of $G$ is minus the sum of off-diagonal exit rates; its marked off-diagonal entry is zero and its other off-diagonal entries are the rates. The definitions `variance`, `randomness` and `skewness` use these $t_n$ in the formulas above.

1. **A valid concrete network.** The private definition `rates` has states $0,\ldots,7$, marked release $7\to0$, and precisely these nonzero rates: $k_{01}=75$, $k_{02}=25$, $k_{17}=25$, $k_{23}=k_{34}=k_{45}=k_{56}=k_{67}=5$, and $k_{70}=25$. For these fixed rates and endpoints, `network` proves nonnegative off-diagonal rates, a positive marked rate, and reachability of state $7$ from every state, including its own path of length zero.
2. **Invertibility and moment certificates.** For this same fixed network, `cemetery_eq` identifies $A$ with the private matrix `a`, and `determinant_unit` proves that its determinant is a unit, using upper triangularity and diagonal entries $100,25,5,5,5,5,5,25$. The lemma `moment_step` applies to every $n\in\mathbb N$ and every vector $v:\mathrm{Fin}\,8\to\mathbb R$ satisfying $av=(n+1)m_n$ for these fixed rates and endpoints; it concludes $m_{n+1}=v$. The lemmas `first_moment`, `second_moment` and `third_moment` certify the fixed vectors `v1`, `v2` and `v3`; `moment_values` gives $t_1=33/100$, $t_2=1673/5000$ and $t_3=234843/500000$ at reset state $0$.
3. **The violated implication.** For these fixed rates and endpoints, `variance_value` gives $\sigma^2=2257/10000$ and `randomness_gt` gives $\mathcal R>1$. The lemma `skewness_le` proves $\mathcal S\le2$: the square root of this positive variance is at least $19/40$, and the third central moment $105153/500000$ is at most twice $(19/40)^3$. The theorem `result` applies the proposed universal implication to this network with its positive variance and skewness bound, contradicting `randomness_gt`.

## Falsifier

The refutation would not answer the source question if the moment encoding or admissible witness differed from cycle completion at product release. The following boundaries matter:

- `moment` is defined by matrix inversion and natural recursion, including for singular matrices; the module does not construct a stochastic process or prove a general equality with integrals against the source's $\psi(t)$. Invertibility is certified for the witness by `determinant_unit`, rather than assumed from this total definition.
- `IsNetwork` imposes no diagonal-rate condition and does not require $p\ne r$. The witness has zero diagonal rates, distinct endpoints $7$ and $0$, and an irreversible marked release, so neither extra freedom supplies its counterexample.
- The source fixes the release rate to one; the witness uses rate $25$. Rescaling all rates by $1/25$ gives release rate one and preserves $\mathcal R$ and $\mathcal S$, by the scaling argument under Triage.
- The source itself allows zero backward rates in its multicyclic example (lines 333–335). The witness also uses irreversible non-product transitions.

The probabilistic interpretation for this particular forward network is explained under Triage. A general formal bridge from matrix moments to stochastic waiting times remains outside the module.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`, with `claim : Prop`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:ed75a3b1ceeaadac68eae831ea10d67ba09f88da305e3de480c68122ec48c550`;
- `claim`: `sha256:4767dbb0bb7fd31ae519d6c0ae1fbe670e6e6fa96864b7cd2afd6f9d57a3227f`.

## Triage

Tier 1 open question of a 2015 paper, preregistered in issue #26046 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that for every $m\in\mathbb N$, rate function $k:\mathrm{Fin}\,m\to\mathrm{Fin}\,m\to\mathbb R$ and endpoints $p,r\in\mathrm{Fin}\,m$, nonnegative off-diagonal rates, a positive marked rate $k_{pr}$, reachability of $p$ from every state by positive-rate paths, positive `variance`, and `skewness` at most two imply `randomness` at most one, where the moments and statistics are the module's matrix-based definitions.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Waiting-time interpretation.* At reset state $0$, the holding time is exponential with rate $100$, independently of the branch choice: competing rates $75$ and $25$ choose the fast and slow routes with probabilities $3/4$ and $1/4$. The fast route has one exponential holding time of rate $25$ before reaching $7$; the slow route has five independent exponential holding times of rate $5$. Both finish with the independent release holding time at $7$, exponential with rate $25$. These statements follow directly from the independent exponential races defining a continuous-time Markov chain. Conditioning on the branch and adding independent holding times gives its completion-time distribution. For this network, let $f_i(s)=\mathbb E_i[e^{-sT}]$ and $q_i=\sum_{j\ne i}k_{ij}$. Conditioning on the first holding time and its destination gives $(q_i+s)f_i(s)=\sum_{j\ne i,\,(i,j)\ne(p,r)}k_{ij}f_j(s)+\mathbf1_{i=p}k_{pr}$. Every path uses finitely many exponential holding times with positive rates before release, so all moments are finite and the Laplace transforms can be differentiated at zero. Differentiating this identity $n\ge1$ times and using $m_n(i)=(-1)^n f_i^{(n)}(0)$ gives $q_i m_n(i)-\sum_{j\ne i,\,(i,j)\ne(p,r)}k_{ij}m_n(j)=n m_{n-1}(i)$. Invertibility makes this system's solution exactly the recursive matrix definition. This supplies the interpretation for the witness without asserting a formal stochastic-process theorem.
- *Mechanism.* The routes have different conditional mean durations, and the five-stage slow route has squared coefficient of variation $1/5$, rather than the value one of a single exponential holding time. The identity $\operatorname{Var}(T)=\mathbb E[\operatorname{Var}(T\mid B)]+\operatorname{Var}(\mathbb E[T\mid B])$, where $B$ is the route choice, shows the separate contribution of the separation between the routes. There is no corresponding requirement that the standardized third moment exceed two. The missing structural restriction is control of the distribution of route durations; merely requiring a finite network and an accessible product edge permits this mixture. A single exponential trapping state, as in the source's off-pathway example, does not represent the five-stage slow route.
- *Time normalization.* For a network with positive mean and variance and invertible negative cemetery generator $A$, and any positive scalar $c$, replacing every rate by $c$ times that rate replaces $A$ by $cA$ and $A^{-1}$ by $c^{-1}A^{-1}$. Induction in the moment recursion therefore replaces $t_n$ by $c^{-n}t_n$; variance and the third central moment scale as $c^{-2}$ and $c^{-3}$. With positive variance, the factors cancel in both $\mathcal R$ and $\mathcal S$. Taking $c=1/25$ puts the witness on the source's release-rate convention.
- *Nearby statements.* The witness is multicyclic and does not challenge the source's unicyclic randomness bound or its proposed unicyclic skewness and kurtosis bounds. The source describes the latter bounds as supported by numerical optimization for $2\le N\le8$ and analytical evidence including $N=2$ (lines 195–214); no general proof of them is supplied by this settlement. Whether the implication holds throughout the source's four-state two-route topology or its off-pathway specialization remains open here. The kurtosis-versus-skewness part of the ordering, the infinite family and its limits, and reversible perturbations are not settled by `result`.
- *Effect on the paper.* The arbitrary-network extension of the detection ordering cannot be used: the certified randomness-versus-skewness implication already has a counterexample. The kurtosis of the witness is not part of the Lean theorem. The source's numerical observations for its specified four-state schemes are not contradicted, and its conclusion that higher moments can reveal information absent from randomness does not require universal dominance. Its separate questions about substrate-concentration formulas and reversible product-count statistics (lines 376–382) remain unanswered here.

## ASSUMED-UNVERIFIED

The bounded literature check in #26046 does not establish exhaustive worldwide novelty or priority. The cited works and citation trails were reported by the preregistration's search author and have not been independently reread here; the four subscription-only papers remain unread. The issue's claim that v1 is the only arXiv version and its historical repository search have not been independently reproduced.

The statements under "Argued, not formalized" are outside the formal conclusion of `result`; in particular the positivity of the skewness, the fourth moment, the kurtosis, the probabilistic interpretation, the rate-scaling argument and the discussion of surviving source claims are not formalized. The search author's family-limit and reverse-rate-perturbation readings recorded in #26046 have not been reproduced here and are not used. No general stochastic-process correspondence, universal replacement hypothesis, minimal-state counterexample, or settlement of the source's restricted four-state cases is claimed.
