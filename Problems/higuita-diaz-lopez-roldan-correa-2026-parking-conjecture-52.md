---
slug: higuita-diaz-lopez-roldan-correa-2026-parking-conjecture-52
bibkey: higuitadiazlopezroldancorrea2026parking
doi: null
url: https://arxiv.org/abs/2611.14718v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.not_conjecture52
---

# Stochastic dominance in discrete parking on subcubic graphs

## Problem

Higuita-Diaz, López and Roldán-Correa ask whether sequential occupancy
stochastically dominates static occupancy for every finite simple graph
of maximum degree at most three. The comparison is first-order stochastic
dominance of the terminal occupancy count. [Conjecture 5.2](https://arxiv.org/html/2611.14718v2#S5.Thmtheorem2)

| Source clause | Lean counterpart |
| --- | --- |
| Every finite simple graph | Every finite vertex type with decidable equality and every Mathlib simple graph with decidable adjacency |
| Maximum degree at most three | `G.maxDegree ≤ 3` |
| Static occupancy | `Parking.static` filters the finite power set by `Maximal G.IsIndepSet` and uses the uniform ratio in equation (3) |
| Sequential occupancy | `Parking.seq` chooses uniformly from the available set, then `Parking.after` deletes that vertex and its neighbors. Conditioning expands to the ordered products in equations (2) and (4) |
| Stochastic dominance | `seq G k Finset.univ ≤ static G k` for every nonnegative integer cutoff in Definition 2.1, represented by a natural number |
| Negation of the universal conjecture | `Parking.not_conjecture52 : ¬ Parking.Conjecture52` |

## Motivation

The set of possible terminal configurations is the same in both models. The
static law assigns a uniform mass to each configuration. The sequential law
assigns total mass over the orders that generate each configuration.
A size comparison detects whether the resulting bias favors larger or
smaller configurations.

## Gap

The first-tier preregistration inspected the source, the authors' code and
related arXiv and repository results. It found no earlier witness in that
scope. OpenAlex returned HTTP 429, and priority remains unverified.
[Preregistration #35265](https://github.com/the-omega-institute/trureturing/issues/35265)

## Route

On vertices 0 through 14, take the edges (0,7), (1,8), (2,9), (3,10),
(4,11), (0,12), (1,12), (5,12), (2,13), (3,13), (6,13), (4,14),
(7,14) and (9,14). The edge list gives a connected graph with 14 edges,
so it is a tree. The Lean degree check uses Mathlib's maximum-degree bound
from pointwise degree bounds.

The static computation checks independence and coverage by closed
neighborhoods, which together characterize maximal independent sets. The
sequential computation splits on the first chosen vertex and evaluates
the conditional averages on the resulting available sets.

## Falsifier

At cutoff six the static CDF is $1/55$ and the sequential CDF is
$64/3375$. The difference $29/37125$ is positive.

## Evidence

The settling GID is
`D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.not_conjecture52`.
The checked statement is the literal negation of the compiled Prop
`Parking.Conjecture52`. The static and sequential CDF certificates are
private proof inputs to this theorem. Its axiom closure is
`propext`, `Classical.choice` and `Quot.sound`.

## Triage

Admission uses `open-problem-resolution` through #35265. The proof uses
a concrete graph construction and exact finite computation.

### What the settlement shows

- **Proved by the settling GID.** Maximum degree three does not guarantee
  that sequential occupancy stochastically dominates static occupancy.
  The checked witness has maximum degree three and reverses the comparison
  at cutoff six. Its tree property follows from the edge-list calculation.
- **Computed by exact rational enumeration.** There are 55 maximal
  independent sets with size histogram 1, 50, 4 at sizes 6, 7, 8.
  The entire lower tail at six is the single set
  $\{8,10,11,12,13,14\}$. Summing the product of the reciprocal
  available-set sizes over its 720 orders assigns it mass $64/3375$,
  only $29/37125$ above its uniform mass of $1/55$ and about 4.30 percent
  higher relative to that mass. An imbalance this small at the bottom of
  the size distribution suffices to reverse the lower-tail inequality.
  The individual sequential masses vary from $1/160$ to $569339/10135125$.
- **Computed by the full terminal law on the same graph.** At seven the
  CDFs cross back. The static CDF is $51/55$ and the sequential CDF is
  $8185211/10135125$. Neither occupancy stochastically dominates the
  other on this example. The mean sequential occupancy exceeds the
  static mean by $1204897/10135125$.
- **Proved in the source.** Theorem 3.1 and Proposition 4.2 establish
  the proposed dominance on paths and cycles. Every finite simple graph
  of maximum degree at most two is a disjoint union of paths, including
  isolated vertices, and cycles. The source's Corollary 6.3 combines
  these componentwise comparisons. Thus two is the largest uniform
  degree threshold for the proposed direction. This sharpness argument
  uses the source theorems for the positive side.
  [Path and cycle results](https://arxiv.org/html/2611.14718v2#S3.Thmtheorem1)
  [Cycle proposition](https://arxiv.org/html/2611.14718v2#S4.Thmtheorem2)
  [Component comparison](https://arxiv.org/html/2611.14718v2#S6.Thmtheorem3)
- **Open here.** The paper's finite ladder-grid dominance and mean
  comparisons can no longer be inferred from Conjecture 5.2. This graph
  gives no counterexample within the ladder family. The reported positive
  tests through order 12 leave the minimum possible witness order
  unresolved here. [Source conjecture discussion](https://arxiv.org/html/2611.14718v2#S5.SS4)

## ASSUMED-UNVERIFIED

Literature-search completeness and publication priority remain ASSUMED-UNVERIFIED.
The bounded screen recorded in #35265 covers the source, the authors' code, and
related arXiv and repository results. OpenAlex returned HTTP 429, leaving citation
coverage incomplete. The minimum order of a subcubic counterexample remains open.
