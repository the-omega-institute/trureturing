---
slug: halliwell-mawby-2019-leggett-garg-six-time-sufficiency
bibkey: halliwellmawby2019finentimes
doi: 10.1103/PhysRevA.100.042103
url: https://arxiv.org/abs/1906.04865v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.result
---

# Polygon and three-time Leggett–Garg inequalities are insufficient at six times

## Problem

J. J. Halliwell and C. Mawby, *Fine's theorem for Leggett-Garg tests with an arbitrary number of measurement times*, Phys. Rev. A 100, 042103 (2019), arXiv:1906.04865v2, Section 4.B, “Sufficient Conditions: A Conjecture”, state:

> A set of sufficient conditions for the existence of a joint probability matching all possible pairwise probabilities consists of the $n$-gon equalities Eq.(\ref{neweq}) together with all possible three-time LG inequalities of the form
>
> $1 + s_i s_j C_{ij} + s_i s_k C_{ik} + s_j s_k C_{jk} \ge 0,$
>
> where $i<j<k$.

This quotation is from the downloaded v2 e-print member `LGn_paper_revised.tex`, lines 554–559, md5 `9f186d04357875722ffef09fcdb26481`. The word “equalities” is in the source; the referenced Eq. (neweq), lines 494–512, states the inequalities
$n+2\sum_{i<j}s_is_jC_{ij}\ge1$ for odd $n$ and $\ge0$ for even $n$, for all signs $s_i\in\{\pm1\}$. Section 4.B assumes nonnegative pairwise probabilities, and the shared-time compatibility condition is Eq. (cons), lines 150–153.

Issue [#23609](https://github.com/the-omega-institute/trureturing/issues/23609) fixes the assertion: for every $n\ge3$, every family of nonnegative normalized pair tables compatible on shared times has a matching joint probability whenever its correlators satisfy all full-set $n$-gon inequalities and all three-time LG inequalities. This assertion is refuted by a six-time family. The source and its pairwise setting are documented in [the literature note](../Library/Observer/halliwellmawby2019finentimes.md).

## Motivation

The proposed sufficiency criterion would decide whether all $n(n-1)/2$ pairwise probability tables can arise from one classical stochastic law. Its failure separates positivity and compatibility of the individual snapshots, together with the listed correlation inequalities, from consistency of the full family with a joint probability.

## Gap

Issue #23609 records the literature check before any Lean:

- The source v2 states the conjecture and establishes the symmetric cases $n=4$ and $n=5$; these restrictions are explicit at TeX lines 565–566.
- The search report lists 17 OpenAlex citations and 18 OpenCitations records, and reports screening 16 citing arXiv full texts and one MDPI paper, including Halliwell and Mawby, arXiv:2101.12266; no refutation or correction of Section 4.B was found in that scope, and one publisher text was unreachable.
- The preregistration reports no earlier repository reference to arXiv:1906.04865 in the searched issues, `D5/`, `Library/` or `Problems/`.

`not-found-in-searched-scope`.

## Route

Use time labels $1,\ldots,6$ for the Lean indices $0,\ldots,5$. Set $C_{i6}=1/2$ for $i=1,2,3,4$, $C_{56}=-1/2$, and $C_{ij}=0$ for the remaining distinct pairs. Define $p_{ij}(a,b)=(1+abC_{ij})/4$ for sign outcomes $a,b\in\{\pm1\}$.

1. **The pair family.** For this fixed six-time `p`, `p_family` establishes nonnegative entries and normalization for every $i<j$, with both one-time marginals equal to $1/2$. For every pair of Lean indices $i,j\in\mathrm{Fin}\,6$, `p_corr` computes `corr p i j`; its values at $i<j$ are exactly the specified $C_{ij}$. The theorem `p_ngon` checks the full six-gon inequality for every six-sign assignment; `p_three` checks the three-time inequality for every $i<j<k$ and every triple of signs.
2. **The weighted square.** For the fixed coefficients $b=(1,1,1,1,-1,-2)$, put $W(x)=\sum_i b_i x_i$. For every six-sign assignment $x$, `weight_sq_expand` gives $W(x)^2=\sum_i b_i^2+2\sum_{i<j}b_ib_jx_ix_j$, and `weight_sq_lower` gives $W(x)^2\ge1$.
3. **What matching marginals force.** Let $\mu:\{\pm1\}^6\to\mathbb R$ match this fixed `p` at every $i<j$ and every pair of outcomes. Under precisely these marginal identities, `sum_mu_one` gives $\sum_x\mu(x)=1$, `pair_expect` gives $\sum_x\mu(x)x_ix_j=C_{ij}$ for each $i<j$, and `weighted_square_sum` gives
   $\sum_x\mu(x)W(x)^2=(\sum_i b_i^2)(\sum_x\mu(x))+2\sum_{i<j}b_ib_jC_{ij}$.
   These three lemmas do not require $\mu$ to be nonnegative.
4. **The contradiction.** If such a matching $\mu$ is also nonnegative at every assignment, `p_no_joint` combines the pointwise lower bound with unit mass to obtain $\sum_x\mu(x)W(x)^2\ge1$, whereas the marginal expansion evaluates the same sum to $9+2(-5)=-1$. Applying `claim` with $n=6$ and this `p` would supply that impossible $\mu$, yielding `result : ¬ claim`.

## Falsifier

The refutation must concern the source's pair probabilities, rather than an unrelated correlation relaxation. The module's `PairTables n` contains real tables, with conditions imposed only at $i<j$; `IsPairFamily` requires nonnegativity, normalization and common one-time marginals. The function `corr` sums the product of the two outcome signs against each table. Boolean `true` represents $+1$ and `false` represents $-1$ through `IsingUniquenessSets.sgn`.

`NGonInequalities` quantifies over every full-set sign assignment, and `ThreeTimeLG` over every ordered triple $i<j<k$ and all signs. Polygon inequalities on other subset sizes are not additional hypotheses of `claim`.

`HasJointDistribution` asks for a nonnegative real mass function with every specified pair marginal. It does not separately assert unit mass; for any real mass function matching this six-time `p` at every $i<j$ and all outcomes, `sum_mu_one` obtains unit mass from the normalized pair at Lean indices $0,1$. The claim imposes no quantum-realizability assumption.

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.lean`.

- **Proof.** It defines `PairTables`, `IsPairFamily`, `corr`, `NGonInequalities`, `ThreeTimeLG`, `HasJointDistribution` and `claim`, and proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:087e0588430e3c1c70a684c94e56fe7fe414101be98aa73cbc223d2c81511e3e`;
- `claim`: `sha256:651f81414e5c32463eb3a1ae12ae625ecd0a0464a9f973ccc9eb48a51120131a`.

## Triage

Tier 1 conjecture of a 2019 paper, preregistered in issue #23609 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every $n\ge3$ and every compatible family of normalized nonnegative pair tables, the full-set $n$-gon inequalities and all three-time LG inequalities imply a matching nonnegative joint distribution.

**Computed, not formalized** (orchestrator, recorded in #23609): the six-time family satisfies the polygon inequality of every subset of at least three times under every sign pattern.

**Argued, not formalized**.

- *Missing weighted constraints.* For any jointly distributed signs $Q_i$ and any real coefficient vector $c$, $\mathbb E(\sum_i c_iQ_i)^2\ge0$. Thus their second-moment matrix, with diagonal one, must be positive semidefinite. The polygon tests use coefficients of equal absolute value on their support and can miss other directions. Positive semidefiniteness excludes this example, whose specified correlations give a negative weighted square; whether adding it to the proposed inequalities suffices at six times is not settled here.
- *Symmetry does not repair the criterion.* The specified pair tables are invariant under simultaneous reversal of both signs. If a matching joint law existed, averaging it with its global sign reversal would preserve these tables and make every odd moment vanish. Consequently the obstruction also concerns the source's symmetric setting.
- *Every proper restriction can still have a joint law.* If the centre time $6$ is omitted, independent fair signs realize the remaining zero correlations. If one leaf time is omitted, let four signs $Y_i$ be uniform over the eight assignments with $S=\sum_iY_i=\pm2$, and set the centre sign to $S/2$. Global reversal gives zero means. Exchangeability and $\mathbb E S^2=4$ give $4+12\mathbb E(Y_iY_j)=4$, so distinct leaves have zero correlation, and $\mathbb E(Y_iS/2)=1/2$. Reverse the retained leaf with negative centre correlation, if present. These means and correlations give exactly the required binary pair tables. Further restrictions follow by marginalization; the separate laws need not extend to one six-time law.
- *Quantum scope.* For the symmetrized operator correlators specified in Section 4.A, TeX line 536, Hermitian dichotomic operators $\hat Q_i$ in a positive normalized state give $c^{\mathsf T}Rc=\langle(\sum_i c_i\hat Q_i)^2\rangle\ge0$, where $R$ has diagonal one and the specified off-diagonal correlators. The present matrix violates this necessary condition. It therefore cannot be realized by that operator formula; other temporal measurement models are not settled here.
- *Effect on the source.* The complete characterization conjectured in Section 4.B and repeated in the summary, TeX line 913, cannot be used at six times. The source's necessity argument for the polygon inequalities, its restricted symmetric $n=4,5$ sufficiency results, and its theorem for the smaller cyclic set of measured pairs are not contradicted. Its large-$n$ analysis of violations of the listed inequalities does not thereby characterize all failures of joint realizability when all pair tables are fixed.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The citation counts, screening of citing texts including arXiv:2101.12266, unreachable publisher text and repository search results are reported in #23609 and were not independently reproduced here.

The subset-polygon enumeration, positive-semidefiniteness and operator arguments, symmetrization argument, proper-restriction construction and discussion of consequences for the source are not formalized. The source's separate theorems are not re-formalized by this module. A complete sufficiency criterion for $n\ge6$, sufficiency after adding positive semidefiniteness, the general nonsymmetric cases at smaller $n$, and realizability under other temporal quantum measurement models are not settled here.
