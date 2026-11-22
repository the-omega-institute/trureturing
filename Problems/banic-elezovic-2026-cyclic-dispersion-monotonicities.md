---
slug: banic-elezovic-2026-cyclic-dispersion-monotonicities
bibkey: banicelezovic2026cyclic
doi: 10.48550/arXiv.2611.14735
url: https://arxiv.org/pdf/2611.14735v1#page=15
triage: theorem
motivation_gids:
  - D5/S3/TotalVariation/BanicR312Settlement.result
---

# The two proposed monotonicities of cyclic multinomial dispersion

## Problem

Nikola Banić and Neven Elezović, *Discrete total variation under the
multinomial, Part 5: cyclic total variation*, arXiv:2611.14735v1, Remark 3.12,
p. 15, ask whether exact cyclic dispersion increases with sample size and
decreases with the number of bins. Draw $N$ independent labels uniformly
from $n$ bins and let $X_i$ be the counts. For natural numbers $n\ge3$
and $N\ge1$, set $X_{n+1}=X_1$, $D=\sum_{i=1}^n |X_{i+1}-X_i|$,
$v(n,N)=\operatorname{Var}(D)/N$, and $\sigma_c(n,N)=\sqrt{v(n,N)}$.
The two author clauses in the registered conjunction are

$$
\bigl[\forall n\ge3,\ N\ge1,\ \sigma_c(n+1,N)\le\sigma_c(n,N)\bigr]
\ \land\
\bigl[\forall n\ge3,\ N\ge1,\ \sigma_c(n,N)\le\sigma_c(n,N+1)\bigr].
$$

The adjacent comparisons express global weak monotonicity on the integer
domains. Corollary 3.5 treats convergence toward the fixed-bin limit.
Remark 3.13 separately asks about modes in the all-bin profile at a
fixed sample size.
[Published statement](https://arxiv.org/pdf/2611.14735v1#page=15) ·
[Library citation and rights](../Library/TotalVariation/banicelezovic2026cyclic.md) ·
[Registered statement](https://github.com/the-omega-institute/trureturing/issues/31389)

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Bounded count carrier with all subsets measurable | `CountVector` and `countVectorMeasurableSpace` |
| Uniform multinomial counts of total \(N\) | `multinomialMass` vanishes off total \(N\), and `multinomialLaw` sums the weighted Dirac measures |
| Cyclic variation with the closing edge | `cyclicVariation`, with `finRotate` |
| Cyclic dispersion at \((n,N)\) | `dispersion`, the square root of `dispersionSquared` |
| Decreases as the bin count increases | First conjunct of `claim`, for every natural \(n\ge3\) and \(N\ge1\) |
| Increases as the sample size increases | Second conjunct of `claim`, on the same domain |
| Refutation of the conjunction | `result : ¬ claim` |

## Motivation

Cyclic closure includes the edge between the last and first bins, so the
second moment includes joint contributions from count differences on
the same multinomial realization. The source's first-order approximation
gives a decreasing profile in the bin count, and its fixed-bin expansion
describes the approach as the sample size grows.
[Part 5 v1, Corollary 3.5](https://arxiv.org/pdf/2611.14735v1#page=11) ·
[Part 5 v1, Proposition 3.7](https://arxiv.org/pdf/2611.14735v1#page=12)

## Gap

The asymptotic arguments in Remark 3.12 leave both exact global
inequalities unresolved. A fixed-bin remainder estimate must control
the relevant differences to compare exact dispersions. A finite
reversal identifies a failure of monotonicity without characterizing
the large-sample ranges or the global fixed-sample mode.
[Part 5 v1, Remarks 3.12–3.13](https://arxiv.org/pdf/2611.14735v1#page=15)

## Route

The count carrier has the top measurable space and is the function type from $\operatorname{Fin}(n)$ to
$\operatorname{Fin}(N+1)$. A vector receives weight zero unless its counts
sum to $N$. On that total the measure puts mass
$N!\,n^{-N}/\prod_i X_i!$ on the vector by a weighted Dirac sum. Each count
is at most $N$ because the counts are nonnegative and sum to $N$.
Mathlib's `finRotate` supplies the cyclic successor. The edge differences
are real differences before absolute value. Lean uses
`ProbabilityTheory.variance` under that measure, divides by $N$, and
applies `Real.sqrt`.

For a fixed pair $(n,N)$, sum the integer multinomial weight times
$D^j$ for $j=0,1,2$. The integer weight agrees with the factorial weight
by `Nat.multinomial_spec`. Multiplying the zeroth sum $n^N$ by $n^{-N}$
normalizes the measure. The Dirac integrals of $D$ and $D^2$ give the
first and second moments. Mathlib's `variance_eq_sub` gives the second
moment minus the square of the first. Division by $N$ and
`Real.sqrt_lt_sqrt` give the dispersion comparison.

## Falsifier

At four draws, increasing the number of bins from three to four gives
$v(3,4)=644/729<247/256=v(4,4)$. The strict difference is
$15199/186624$. Taking square roots gives
$\sigma_c(3,4)<\sigma_c(4,4)$, contradicting the first author clause.
The public theorem `result : ¬ claim` applies this comparison directly to
the first projection of the conjunction.

At four bins, increasing the draw count from four to five gives
$v(4,5)=3835/4096<247/256=v(4,4)$. The decrease is $117/4096$.
Taking square roots gives $\sigma_c(4,5)<\sigma_c(4,4)$, independently
contradicting the second author clause. The scratch module
`BothReversals` proves this clause false as
`D5.S3.TotalVariation.BanicR312Settlement.samples_not_monotone`.
The public refutation uses the bin-count counterexample alone.

## Evidence

| Bins | Draws | Weighted sums of $1,D,D^2$ | $v(n,N)$ | Evidence |
| --- | --- | --- | --- | --- |
| 3 | 4 | $(81,312,1488)$ | $644/729$ | Kernel-checked in the proof of `result` and in the independent bin-count check |
| 4 | 4 | $(256,1120,5888)$ | $247/256$ | Kernel-checked in the proof of `result` and in both independent checks |
| 4 | 5 | $(1024,5040,29600)$ | $3835/4096$ | Kernel-checked in the independent sample-size check |

### Provenance and rights

- Nikola Banić and Neven Elezović posed the two questions in Remark 3.12
  of arXiv:2611.14735v1, PDF p. 15. The v1 record specifies arXiv's
  perpetual, non-exclusive distribution license, which grants arXiv.org
  distribution rights. The dossier uses independent prose and mathematical
  notation. [Remark 3.12](https://arxiv.org/pdf/2611.14735v1#page=15) ·
  [Version record](https://arxiv.org/abs/2611.14735v1) ·
  [License text](https://arxiv.org/licenses/nonexclusive-distrib/1.0/)
- Claude Code session `07b67e50-10a4-41b3-9622-660f37c654a5`
  coordinated the historical research. Codex CLI research flight
  `8964c4b7bb607dfbb7e139d9` prepared the bounded literature screen, the exact
  experiment, the mathematical derivation and the compiled definitions.
  GPT Pro search seat `gptpro-search-s1318` contributed literature search.
  Loning is the Git author of the experiment commits `b8dc43bcdef0` and
  `ff95ccea7230`. The issue and experiment give the original rational
  witnesses for both reversals. The experiment enumerates labelled
  histories and checks the factorial weights, moments and rational
  differences. Its output ends in `ALL_CHECKS_OK`, and the program's
  SHA-256 is `c2090893aea833f7693f832fd42aeee798d81120d2927d26d526c9c3ed422cd8`.
  [Research attribution and witnesses](https://github.com/the-omega-institute/trureturing/issues/31389) ·
  [Exact experiment at ff95ccea](https://github.com/the-omega-institute/trureturing-experiments/tree/ff95ccea7230a44f5e84e8b81f944ccb6d926881/docs/reports/banic2611r312)
- Codex CLI proof flight `6b02a23c137ce8bf24560049` authored the original
  Lean proof of the three exact variance equalities and both strict
  square-root comparisons. Its archived source has SHA-256
  `cf70109571fae7f367a16af7f59dff458b3a483973bf4297de1495b12856e80b`
  and matches the Lean blob at `23991cf8468c143c94cb0ad21d1680f59fb70936`.
  Git records MacStudio2 on that checkpoint and on the follow-up
  `e2d7e21e2b467a22fdefd3685428502a6344e892`.
  [Scoped probe registration](https://github.com/the-omega-institute/trureturing/issues/31389#issuecomment-7076300413)
- Codex CLI Stage A flight `6b02a69d3e9dff94a3d5d1b7` integrated the live
  public refutation and its initial Scribe, Library citation and dossier.
  In candidate `c9b9d86c09b70fb978ca20565ebd5832eac1ab22`, Git records
  MacStudio2. The Lean source has SHA-256
  `a57f7f9c4aab61fab65187b8189feb7f73d7ca7c9a18b07be05b03bc475d8739`.
  The theorem `result` applies the strict bin-count comparison to the
  first clause. The same flight compiled the separate `BothReversals`
  module, which uses the original moment derivation to give direct
  contradictions to each clause. The separate source has SHA-256
  `d315ebfe02fd570b1fbbca374fd565a825b2f72b2e01da56543edda277397b63`
  and its replayed object has SHA-256
  `ddb0125afeec0e27e4b62051ecac34471d34e35af2a75d35ffb3c9a4c035a33a`.
- Codex CLI flight `6b02ad5d9985be77a04c7d34` authored the expanded Scribe
  and this provenance account. The Scribe shows the definitions and the
  full negation of the two quantified clauses. Lean expresses the public
  theorem with the literal type `Not claim`.

The completed literature screen covered the pinned source, searches of
Parts 1–4 and relevant small-bin and transfer passages, arXiv title and
author queries, repository and indexed-code queries, MathOverflow and
Zenodo. It located no settlement of these finite-sample assertions in
those sources. Alexander Stephen Donahue of 0thernes LLC resolves Part 2
v1 Conjecture 7.7, the adjacent triangular-lattice constant, as
`MultinomialTV.conjecture_7_7` in his separate manuscript and Lean
development. The corresponding conditional coefficient in Part 5 v1
is **Theorem 3.10**, p. 14.
[Donahue’s manuscript and Lean source at df6cab4b](https://github.com/0thernes/multinomial-tv-conjecture/tree/df6cab4b2b6cef7910f1990234741a328e52ea40) ·
[Part 2 v1](https://arxiv.org/abs/2610.17046v1) ·
[Part 5 v1 Theorem 3.10](https://arxiv.org/pdf/2611.14735v1#page=14)

## Triage

- **Lean proved.** `D5/S3/TotalVariation/BanicR312Settlement.result`
  refutes the conjunction in Remark 3.12 with both original quantified
  clauses and the exact uniform law. Its `proof_shape: content` comes
  from evaluating the exact weighted moments for the bin-count reversal.
  This is a Tier 1 named external question with
  `admission_basis: open-problem-resolution`.
  [Preregistration](https://github.com/the-omega-institute/trureturing/issues/31389)
- **Lean proved in separate compiled evidence.** The sample-size clause
  fails at four bins. The exact values $247/256$ and $3835/4096$ give the
  strict variance comparison and hence the strict dispersion comparison.
  The scratch proof directly contradicts that clause.
- **Audit scope.** The designated literal `Not claim` theorem is
  exempt from four-slot registration. It is the sole public theorem in
  the candidate, so there are zero §3.9 registration targets.

### What the settlement shows

- **Derived mechanism and exact checks.** For $M=\sum_i\min(X_i,X_{i+1})$,
  cyclic closure gives $D=2N-2M$. At fixed $N$, dispersion is determined
  by the variance of this occupancy-overlap sum. Adjacent and disjoint
  edges enter that variance through different joint occupancy events.
  The finite moment table exhibits the increase as the fourth bin is
  added. At four bins the equal-count pattern contributes zero variation
  at four draws and is unavailable at five draws. The complete moment
  calculation, including the other count patterns, establishes the
  decrease after the fifth draw.
  [Occupancy calculation and exact distributions](https://github.com/the-omega-institute/trureturing/issues/31389)
- **Surviving source results.** The fixed-bin limit and asymptotic
  expansion in Corollary 3.5 and the no-interior-mode statement for the
  first-order approximation in Proposition 3.7 allow these finite
  reversals. Part 5's linear-statistic ridge expansion in Theorem 4.10
  and conditional second-order cyclic formula in Theorem 3.10 use
  neither exact global inequality.
  [Part 5 v1](https://arxiv.org/pdf/2611.14735v1)
- **Open in this delivery.** Eventual exact monotonicity in the sample
  size at a fixed bin count and a uniform large-sample range for exact
  monotonicity in the bin count remain unresolved here. A global
  fixed-sample mode requires comparison with every other bin count.
  The historical experiment supplies a proposed $N=4$ route for
  Remark 3.13, outside the scope of this Lean refutation.
  [Historical exact calculation](https://github.com/the-omega-institute/trureturing/issues/31389)

## ASSUMED-UNVERIFIED

Exhaustive citation coverage is unverified. The historical OpenAlex exact
record reported zero citations, its citing-works endpoint and the
Semantic Scholar requests returned HTTP 429, and MathDB database
requests returned HTTP 403. The broader arXiv search screened only the
first ten of 201 hits. The classical and applied references listed as
unread in the preregistration remain outside that screen. The historical
$N=4$ all-bin formula and maximizer have no Lean proof in this delivery.
[Bounded searches and limitations](https://github.com/the-omega-institute/trureturing/issues/31389)
