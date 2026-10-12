---
slug: chen-he-lai-li-2026-local-average-dominating-stem
bibkey: chenhelaili2026local
doi: 10.48550/arXiv.2610.11446
url: https://arxiv.org/abs/2610.11446v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/LocalDominatingStemBound.result
---

# Chen–He–Lai–Li Conjecture 6.1: the local average at a stem

## Problem

Tingyun Chen, Weihua He, Hong-Jian Lai and Jianping Li, “On the local average
order of dominating sets”, arXiv:2610.11446v1, Conjecture 6.1:

> Let G be a graph of order n ≥ 2 without isolated vertices, and let v be an
> l-stem of G, where l ≥ 1. Then avd_v(G) ≤ (4n + 1)/6, with equality if and
> only if l = 1 and G is star-like.

A dominating set contains or neighbours every vertex. The local average is
the mean cardinality over the dominating sets containing v. A leaf has
degree one; an l-stem has exactly l leaf neighbours. Literally following
Iain Beaton and Ben Cameron, “A Tight Upper Bound on the Average Order of
Dominating Sets of a Graph”, arXiv:2208.10475v2, a graph is star-like when
every vertex is a leaf or a stem with one or two leaf neighbours.

The closed Lean `claim` quantifies over `V : Type`, its finite and decidable
equality structures, a finite simple graph with decidable adjacency, v and
l. It retains the order, positive-degree and leaf-count hypotheses and both
the upper bound and the equivalence characterizing equality. All averages
are exact rational numbers.

## Motivation

The global bound of Beaton and Cameron is 2n/3. Conditioning on a stem
allows its leaf neighbours to be selected freely and separates the residual
domination constraints. The conjecture asks whether the same global
estimate controls that partial residual family sharply enough to classify
local equality.

## Gap

The v1 source proves strictness for l ≥ 2 in Theorem 5.3 using replicated
residual graphs with a hub carrying two pendant leaves. Theorem 5.2 treats
stems whose neighbours are leaves or stems. Conjecture 6.1 includes the
remaining one-leaf stems with nonstem neighbours. The supplied literature
scope reports no citing work; the Chen–He paper in Advances in Applied
Mathematics (2026) treats vertices of degree n−2, not the general stem
case. This is a scoped finding, not an exhaustive priority claim.

## Route

Let L be the l leaf neighbours of v, and H the induced graph after removing
v and L, of order h=n−l−1. H has no isolated vertices: an isolated residual
vertex would have been another leaf neighbour of v. Let U be the neighbours
of v retained in H. Define A to be the sets internally dominating every
vertex of H outside U, and B the dominating sets of H. Write a=|A|,
b=|B|, α=mean(A), β=avd(H), and c=2h/3. The exact split is

$$
\operatorname{avd}_v(G)=1+\frac l2+\alpha.
$$

B is a nonempty subfamily of A. If a=b, the families coincide and the global
bound gives α=β≤c. If a>b, attach r copies of H to a hub z through the copies
of U, and attach one pendant leaf to z. The resulting graph J_r has order
rh+2 and no isolated vertices. Its dominating sets containing z number
2a^r and have mean 3/2+rα. Those omitting z number b^r and have mean 1+rβ.
The global bound gives

$$
a^r\bigl(1+6r(\alpha-c)\bigr)
\leq b^r\bigl(1+3r(c-\beta)\bigr).
$$

If α≥c, nonnegativity of β implies (a/b)^r≤1+2rh. At
r=4hb²+2, the first three binomial terms give

$$
(1+1/b)^r\geq1+r/b+r(r-1)/(2b^2)>1+2rh,
$$

contradicting a≥b+1. Therefore α<c when a>b. This one-leaf hub extends the
source's two-leaf replication argument to the remaining case.

Consequently the split is at most (4n−l+2)/6≤(4n+1)/6. Numerical equality
forces l=1, A=B and α=c. The concrete one-copy graph J_1 is isomorphic to G;
its exact mean is 2n/3. The Beaton–Cameron equality characterization then
makes G star-like. Conversely, in a star-like graph every residual neighbour
of v retains a leaf neighbour, forcing A=B. For l=1 the global mean
identity gives α=c and hence local equality.

The Beaton–Brown critical-vertex identity and private-neighbour estimate,
the global Beaton–Cameron inequality, and its equality case are all proved
in the prerequisite modules. Equal stem blocks are identified before
summing, including the two descriptions of a two-vertex component.

## Falsifier

The proof requires the stem split to be a bijection, the residual graph and
all replicated graphs to have no isolated vertices, the replicated counts
and size sums to be exact, the ratio denominator b to be positive, and the
strict binomial estimate to have the stated direction. The graph
isomorphism must preserve adjacency. The equality argument must retain the
literal star-like definition. Each obligation is discharged in Lean.

## Evidence

`D5/S3/Combinatorics/Graph/LocalDominatingStemBound.result : claim` is a
closed proof of the complete source statement. Its axiom closure is
`propext`, `Classical.choice`, `Quot.sound`. All three stages compile under
Lean 4.33.0: the global inequality with the Beaton–Brown lemmas, the global
equality case, and the conjecture. There is no `sorry`, new axiom,
`native_decide`, or unchecked numerical approximation in the delivered
modules. Final timing and peak-memory measurements are in `REPORT-avd.md`.

## Triage

`theorem`. The full local bound and equality characterization are proved.

- [proved] The relaxed residual family has mean at most 2h/3. If it properly
  contains the full dominating family, its mean is strictly smaller.
  Replication turns a nonnegative excess into an exponential counting
  ratio, while the global estimate permits only a linear envelope.
- [proved] Local equality requires exactly one leaf neighbour and global
  extremality. The conjecture therefore classifies all local equality
  graphs using the existing global classification. For l≥2 its bound is
  strict, agreeing with the source's Theorem 5.3.
- [proved] The two-thirds global bound and its star-like characterization
  include the empty graph; this handles an empty residual without an
  added nonemptiness assumption.
- [open] Bounds for local averages at vertices without leaf neighbours and
  extremal classifications under further degree constraints are separate
  problems. The source's degree n−2 formula and other results are not
  claimed as formalized here.

## ASSUMED-UNVERIFIED

The literature scope and absence of citing work are supplied with the
problem statement. No independent network survey or exhaustive priority
check is claimed. Kernel compilation and the scoped Scribe checks do not
constitute frozen-ledger publication or an official repository gate;
those actions are outside this delivery's authorized scope.
