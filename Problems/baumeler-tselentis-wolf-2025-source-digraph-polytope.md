---
slug: baumeler-tselentis-wolf-2025-source-digraph-polytope
bibkey: baumelertselentiswolf2025graphical
doi: 10.1016/j.jlamp.2026.101133
url: https://arxiv.org/abs/2511.22552v1
triage: theorem
motivation_gids:
  - D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.result
---

# The source-digraph polytope

## Problem

Baumeler, Tselentis and Wolf, *Graphical Tests of Causality*, arXiv:2511.22552v1,
after Definition 13, state: “We know that $\widetilde Q_n^{\rm src}=Q_n^{\rm src}$
for $n\leq4$. In general, this identity is unsolved.” The settlement is
$\widetilde Q_n^{\rm src}=Q_n^{\rm src}$ for every natural $n\geq2$.
The external question and literal conventions are preregistered in
https://github.com/the-omega-institute/trureturing/issues/20672.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Section 2: vertices $[n]$, arcs $(s,r)$ with $s\ne r$ | `Fin n` and the off-diagonal pair subtype, inlined in the definitions | All loopless directed arcs, with sender first and receiver second. |
| Section 2: adjacency is one exactly on the arc set | The inlined conditional in `sourcePolytope` | Every arc set is a finite set; the empty digraph is included. |
| Theorem 3: some vertex has in-degree zero | `HasSource` | A vertex is never the receiver of an arc in the set. |
| Definition 8: convex hull of source-digraph adjacency vectors | `sourcePolytope` | Real convex hull of precisely those vectors. |
| Definition 13 (58): nonnegative coordinates | First conjunct of `kefalopodaPolytope` | Every arc coordinate. |
| Definition 13 (59): coordinate upper bounds for $n\geq3$ | Second conjunct | No upper-bound hypothesis is added for $n=2$. |
| Definitions 9, 13 (60): every fixed-point-free function gives a sum at most $n-1$ | Third conjunct | One incoming arc per receiver; the bound is real. |
| Identity in every dimension | `claim`, proved by `result` | Every natural $n\geq2$; no bounded enumeration hypothesis. |

The arc subtype and adjacency expression remain inline, while the proof uses
Mathlib's `Set.indicator` for that same adjacency function.

## Motivation

The identity asks whether the trivial and kefalopoda inequalities completely
describe the source-digraph polytope. The source's Section 5 asks whether
kefalopoda inequalities are its only nontrivial facet inequalities.
The Library note is `Library/FiniteGeometry/baumelertselentiswolf2025graphical.md`.

## Gap

The cited v1 source leaves the general identity unresolved. The literature
screen in #20672 found no settlement in its searched scope; completeness is
ASSUMED-UNVERIFIED. The finite-dimensional convex-hull machinery in pinned
Mathlib supplies the convexity and product-box steps, but the inspected D5
sources contain no owner of this source-digraph identity.

## Route

The sole module is
`D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope`.
It has four public definitions, one public theorem `result`, and six private
helpers: `convex_kefalopoda`, `source_subset`, `fixed_source_box`,
`column_maxima`, `box_bound`, and `mixture`.
Its admission basis is `open-problem-resolution (#20672; Proved)`.
All seven theorem proofs are classified bind-only; there is no claimed
escape witness. The six helpers are consumed by the settling proof.
The family is unbounded in $n$ and has no finite numerical certificate payload;
its utility classification is `none`.

For a feasible vector let $m_r=\max_{s\ne r}x_{sr}$. Choosing a maximizer in
each column gives $\sum_r m_r\leq n-1$. Set $c_r=1-m_r$,
$C=\sum_r c_r\geq1$, and $q_r=c_r/C$. Then $q$ is a probability vector and
$q_r\leq1-m_r$. For source $i$, put $y^{(i)}_{sr}=0$ when $r=i$ and
$y^{(i)}_{sr}=x_{sr}/(1-q_r)$ otherwise. These vectors belong to the
fixed-source unit boxes. The equality $\sum_iq_i y^{(i)}=x$ also holds
when a denominator vanishes: $q_r=1$ forces $x_{sr}=0$.
Each box lies in the convex hull of its zero-one source digraphs. Conversely,
a source digraph contributes zero in its source column to any kefalopoda sum,
so the sum is at most $n-1$; convexity extends the inequalities to the hull.

## Falsifier

A counterexample would be a natural $n\geq2$ and a real off-diagonal vector
belonging to exactly one of the two sets. The kernel-checked `result`
excludes that possibility under the displayed definitions. Facet ranks,
worldwide priority, and the lifted correlation polytope are separate claims.

## Evidence

The settling declaration is
`D5.S0.FiniteGeometry.Polytopes.BaumelerTselentisWolfSourceDigraphPolytope.result`.
Its frozen state is
`Golden/Frozen/state/D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.lean.json`.
The Blueprint displays the complete universally quantified identity.

### Independent finite checks

The experiment is [the source-digraph checks at immutable revision
f7a8ca7db5c3303eaccf7cb8869446ee9e2e0176](https://github.com/the-omega-institute/trureturing-experiments/tree/f7a8ca7db5c3303eaccf7cb8869446ee9e2e0176/docs/reports/baumeler-tselentis-wolf-2025-source-digraph-polytope).
The verified `check.py` has SHA-256
`4273bd50fc350edc9e2911c4982aa2594d1a97ed15be14ade928393ac8724da8`.
Command in the experiment repository at that revision:
`python3 docs/reports/baumeler-tselentis-wolf-2025-source-digraph-polytope/check.py`;
the independently rerun bytes have the displayed SHA-256; exit 0.

The numerical rank check finds every kefalopoda inequality facet-defining
for all 8 functions at $n=3$ and all 81 functions at $n=4$.
There are two isomorphism classes at $n=3$.
Vertex enumeration at $n=3$ finds 37 vertices, all source-digraph zero-one
vectors. Exhaustive source-digraph inequality checks cover $n=2,3,4$.
For 1,700 sampled rational points at $n=2,\ldots,8$, including zero columns
and $\sum_r m_r=n-1$, the convex decomposition is exact; the exhaustive
maximum over fixed-point-free functions is checked only for $n\leq6$.
Facet rank and vertex enumeration use floating-point linear algebra;
the decomposition checks use exact rational arithmetic. These finite checks
are computed evidence, not the proof of the unbounded identity.

## Triage

### What the settlement shows

- **Proved, kernel-checked:** `result` states the complete identity for every
  $n\geq2$, including degenerate coordinates. `box_bound` handles $n=2$
  without adding coordinate upper bounds to the source definition.
- **Proved in prose, mechanism:** for $0\leq x\leq1$, the maximum kefalopoda
  sum is $\sum_r\max_{s\ne r}x_{sr}$: every selected entry is at most its
  column maximum, and independent maximizing choices attain the bound.
  The complementary slacks supply the source probabilities in the Route.
  This also describes $Q_n^{\rm src}$ as the convex hull of the $n$
  fixed-source boxes. The argument permits zero weights and $q_r=1$.
- **Proved in prose, consequence for the source:** every facet is supported
  by a trivial or kefalopoda inequality. The identity is a finite
  half-space representation. It is full-dimensional: for $n=2$ take
  both coordinates strictly between zero and $1/2$; for $n\geq3$ take
  all coordinates $\epsilon$ with $0<\epsilon<(n-1)/n$. All inequalities
  are then strict. At a relative interior point of a facet some defining
  inequality is tight; its hyperplane contains that facet, since its
  intersection with the polytope is a proper face containing the point.
  Thus its supporting hyperplane is one of the displayed families.
  This confirms the source's “possibly the only nontrivial” remark in
  that sense; irredundancy and the facet status of each listed inequality
  are not asserted by the Lean theorem.
- **Proved in prose, distinctness mechanism:** the source construction is
  $D_{i,j}=(\{ij\}\cup A(\kappa_f))\setminus\{f(i)i\}$.
  When $ij\in A(\kappa_f)$, adjoining $ij$ changes nothing, so
  $D_{i,j}=A(\kappa_f)\setminus\{f(i)i\}$. Two distinct out-arcs of the
  same vertex $i$ therefore give the same digraph. This is an issue with
  that proposed set of distinct witnesses, not a refutation of the facet
  property.
- **Computed, source Theorem 4 check:** the experiment finds repetitions
  among the proposed digraphs $D_{i,j}$ for 6 of 8 functions at $n=3$ and
  72 of 81 at $n=4$, while all corresponding numerical facet ranks are
  full. This diagnoses that construction's distinctness issue in exactly
  those tested dimensions. A general repaired proof of the source's
  facet theorem is **open here**; the identity does not rely on that proof.
- **Open:** the analogous assertion for the lifted correlation polytope
  $U(Q)$ of Definition 14; no formal implication to it is claimed.
- **Computed evidence scope:** the finite checks and their ranges are exactly
  those in Evidence. Uniform facet-rank claims beyond $n=4$ and experimental
  coverage beyond those ranges are **open here**.
- **Literature boundary:** the source and bounded search are recorded in
  #20672. Worldwide completeness and independent journal Section 5 fidelity
  remain ASSUMED-UNVERIFIED.

The literature screen in #20672 connects the construction to Balas's
convex-hull formulation for unions of polytopes, as discussed by
Conforti–Di Summa–Faenza, arXiv:1711.00891. Eliminating the mixture variables
for the fixed-source boxes gives the displayed identity. This is an
application of existing convexity machinery to the source's named question;
worldwide priority is not asserted. The recorded title, source-digraph,
kefalopoda and weak-causality searches found no settlement in that scope.

The escape audit of the sole public theorem is unfinished:
https://github.com/the-omega-institute/trureturing/issues/21177.
No valid Reg mirror is delivered. The missing obligations are the exact
source-law bridge, whole-family variation, per-role sensitivity,
observational dependence, and source-selection binding evidence for the
varying-dimensional real-coordinate family.

## ASSUMED-UNVERIFIED

The literature search is not exhaustive. The journal's full Section 5 was
not independently retrieved by this implementation seat; the v1 statement
and the source/literature readings in #20672 delimit the external question.
Full texts arXiv:2309.15752, 2410.18735 and 2412.17551v3 were not read in
the recorded screen. Their relationship to this settlement remains unverified.
The finite experiment does not replace the universal Lean proof, establish
exact facet ranks in all dimensions, or settle Definition 14.
