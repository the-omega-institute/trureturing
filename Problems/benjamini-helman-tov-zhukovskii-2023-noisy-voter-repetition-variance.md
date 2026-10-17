---
slug: benjamini-helman-tov-zhukovskii-2023-noisy-voter-repetition-variance
bibkey: benjaminihelmantovzhukovskii2023noisyvoter
doi: 10.1214/23-AOP1637
url: https://arxiv.org/abs/2207.01224
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.result
---

# The repetition-count variance of the noisy voter model

## Problem

I. Benjamini, H. Helman Tov and M. Zhukovskii, *Global information from local observations of the noisy voter model on a graph*, Annals of Probability 51(5), 1963–1992 (2023), Section 2.2, asks:

> May Var(ζ₁ + … + ζ_t) be sublinear? We do not have an answer. However, we prove that it is either linear in t or O(ln t).

The quotation is from arXiv:2207.01224v2, p. 6. The answer is no. For a connected locally finite simple graph with a neighbour at every vertex, noise $0<\varepsilon<1$, observation vertex $u$ of degree $D$ and lag $d\ge1$, put $\zeta_i=\mathbf{1}\{X_i(u)=X_{i+d}(u)\}$ and $W_t=\sum_{i=1}^{t}\zeta_i$. The formal settlement is `D5.S3.StatisticalMechanics.NoisyVoter.RepetitionVarianceLinear.result : claim`. Preregistration: [#16646](https://github.com/the-omega-institute/trureturing/issues/16646). The [Library note](../Library/StatisticalMechanics/benjaminihelmantovzhukovskii2023noisyvoter.md) supplies the publication locator and quotations.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Connected graph, possibly infinite | `G : SimpleGraph V`, `G.LocallyFinite`, `Model.connected` | No finite-vertex restriction; finite neighbour sets make uniform choices meaningful |
| A vertex has a neighbour to copy | `Model.hasNeighbor`; `Value G (Coord.choice k v)` is the neighbour subtype | Excludes an isolated one-vertex graph whose uniform copying law is undefined |
| Independent fair initial opinions | `Coord.initial`, `coordinateLaw`, `Model.independent`, `Model.laws` | Bernoulli one-half |
| Independent fair fresh opinions and Bernoulli noise controls | `Coord.fresh`, `Coord.refresh`, `coordinateLaw`, `Model.ε`, its strict bounds | True means refresh |
| Independent uniform neighbour choices | `Coord.choice`, neighbour-subtype value and uniform finite law | The choice is an actual neighbour |
| Synchronous recursion | `nvm` | Initial, refresh and copying cases mirror Section 1 |
| Repetition indicator at lag $d$ | `W`, sum over `Finset.Icc 1 t`, positive lag in `claim` | No normalization; the observation reaches time $t+d$ |
| Every graph, vertex and probability model | The closed quantifiers of `claim` | Arbitrary vertex type and measurable probability space |
| Variance is never sublinear | `result`, negated little-o in `claim` | Private `model_explicitBound` supplies the explicit lower bound for every natural $t$ |
| Encoding requirements | Decidable equality, measurable-space and local-finiteness instances | Decidable equality is representational; no additional graph hypothesis |

## Motivation

The question distinguishes the linear and logarithmic branches of Lemma 2.3 for a local statistic observed through time. A positive explicit lower bound resolves that variance alternative without resolving graph distinguishability.

## Gap

The source states no answer in its arXiv v2 text. The citation screen recorded in #16646 reads arXiv:2409.03690, 2308.01671 and 2507.16188 and reports no settlement of this temporal repetition-count question. The latter concerns continuous-time spatial test-function variance. Prior-art completeness is `ASSUMED-UNVERIFIED`; the Annals full text was blocked, and the arXiv v2 was read. These are literature readings attributed to the orchestrator in #16646, not a proof of exhaustive novelty.

## Route

Let $A_r$ require a refresh at $u$ at time $r$ and at every neighbour at time $r+1$. On $A_r$, flipping the fresh fair opinion at $(r,u)$ changes no other process value. For centres $r=k(d+1)$, $1\le k\le\lfloor t/(d+1)\rfloor$, it affects exactly the two statistic terms indexed by $r-d$ and $r$.

The masked signed contributions $Z_r$ satisfy $\operatorname{Cov}(W_t,Z_r)=\operatorname{Var}(Z_r)$ and are pairwise orthogonal. Nonnegativity of $\operatorname{Var}(W_t-\sum_r Z_r)$ gives $\operatorname{Var}(W_t)\ge\sum_r\operatorname{Var}(Z_r)$. Requiring one more refresh at $(r+d,u)$ gives a cylinder of probability $\varepsilon^{D+2}$. Pairing its future fair coin with its flip gives a contribution of half this mass. Therefore

$$\operatorname{Var}(W_t)\ge\frac{\varepsilon^{D+2}}2\left\lfloor\frac{t}{d+1}\right\rfloor.$$

The proof constructs the product model with `Measure.infinitePi`, then transports the statistic's law from any `Model` using its independent coordinate laws. No conditional-variance formalization or finite-graph truncation is assumed.

## Falsifier

A model satisfying the closed `claim` with little-o variance would contradict the kernel-checked `result`. A violation of the explicit bound contradicts private `model_explicitBound` on its proof path. The source's graph-distinguishability conjecture has no such conclusion here.

## Evidence

The formal source is [RepetitionVarianceLinear.lean](../D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.lean), with its canonical Blueprint Scribe. Its settling node carries exactly one `OpenProblemResolutionClaim`, of kind `Proved`.

The experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/860c8ed470f95f5f20402602b4bb3c4149b44229/docs/reports/benjamini-helman-tov-zhukovskii-2023-noisy-voter-repetition-variance). Command in that directory: `python3 check.py`; the byte-identical exported script was rerun as `python3 /tmp/op-bhz/experiment-check.py`, exit 0, `ALL_OK`. Script SHA-256: `7de3f127ebb5619e9ecbfc633660d24fec57c6fe72c6eb14e0968c3600ec5311`. Exact rational recursion checks $K_2$, the end and middle of $P_3$, $K_3$, and the leaf and centre of $K_{1,3}$, with $\varepsilon\in\{1/2,1/3\}$. For $d=1$, $1\le t\le10$; for $d=2$, $1\le t\le7$, except $K_{1,3}$ where $1\le t\le6$. Every checked variance satisfies the bound. The reported ratios $\operatorname{Var}(W_t)/t$ range from 0.2006 to 0.5780 at four-decimal display precision. These finite readings do not establish the uniform theorem.

The four-slot escape audits of public `result` and the shared `IsingUniquenessSets.sgn_not` theorem are unfinished: [#16773](https://github.com/the-omega-institute/trureturing/issues/16773). No Reg mirror or `declared_validated` registration is asserted. A lawful enrolled readout for the universal graph/model family, its source reconstruction, and intervention/sensitivity evidence are missing.

## Triage

### What the settlement shows

- **Kernel-checked mechanism:** private `local_erasure` and `local_statistic_difference` isolate the fresh opinion and identify its two incident summands for the selected centres. Private `witness_covariance` and `witness_orthogonal` give the covariance projections and orthogonality. Private `good_integral`, `witness_variance_lower`, `product_explicitBound` and `model_explicitBound` give $\operatorname{Var}(W_t)\ge\sum_r\operatorname{Var}(Z_r)\ge(\varepsilon^{D+2}/2)\lfloor t/(d+1)\rfloor$. Public `result` rules out little-o variance.
- **Proved in prose, using the published upper bound:** Equation (7) of the source gives $\operatorname{Var}(W_t)=O(t)$. Set $q=d+1$ and $c=\varepsilon^{D+2}/2>0$. For $t\ge2q$, $\lfloor t/q\rfloor\ge t/(2q)$, so the formal lower bound gives $\operatorname{Var}(W_t)\ge c t/(2q)$. Combining these bounds gives $\Theta(t)$ variance. The source's Lemma 2.3 therefore always takes the linear branch. Equation (7) and this combined asymptotic statement are literature/prose consequences, not additional Lean theorems in this module.
- **Kernel-checked scope:** private `product_explicitBound` requires local finiteness and a neighbour at every vertex but no connectivity, and its nonnegative bound allows every noise parameter in `unitInterval`. The settled non-sublinearity assertion uses positive noise in `Model`, with the source's connectivity and strict upper bound retained. Infinite locally finite graphs are included directly by the product law.
- **Computed:** the pinned experiment checks exactly the graph/vertex/noise/lag/time ranges in Evidence and returns `ALL_OK`; it supplies no claim outside those finite ranges.
- **Open:** the source's main conjecture, NVM-distinguishability of non-isomorphic finite rooted graphs, remains unresolved here. The exact asymptotic variance coefficient and sharpness of the explicit constant are also unproved here. Variance of order $t$ establishes an order-$\sqrt t$ standard deviation, not a central limit theorem, typical fluctuation statement or a distributional limit.
- **Literature reading, completeness `ASSUMED-UNVERIFIED`:** the arXiv v2 source was read; the Annals full text was blocked. The citation screen and unread Granovsky–Madras/Gordin ingredients in #16646 leave prior-art completeness unresolved.

No other source theorem is re-proved or newly claimed. The logarithmic variance alternative is eliminated in the stated setting; any further inference about graph distinguishability or fluctuation distributions requires its own argument.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The source and citation readings attributed above are the orchestrator's recorded checks in #16646. The Annals full text was blocked; arXiv v2 supplies the quotations and model. The unfinished escape registration in #16773 remains an audit boundary. The finite experiment and published upper bound are separate evidence from the kernel-checked lower bound and closed result.
