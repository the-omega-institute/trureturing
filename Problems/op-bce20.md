---
slug: op-bce20
bibkey: barrettcameronevanshallkempton2022laplacianspread
doi: 10.1016/j.laa.2023.01.016
url: https://arxiv.org/abs/2206.15410v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.result
---

# No universal slope-one bound for digraph Laplacian spread

## Problem

Barrett, Cameron, Evans, Hall and Kempton, *On the Laplacian spread of
digraphs*, arXiv:2206.15410v1, Conjecture 20 in the HTML rendering
(Conjecture 6.7, page 16 of the PDF), states:

> The bound on the Laplacian spread of digraphs given in (3.2) can be reduced to a linear function in n with a slope of 1.

Equation (3.2) is $\operatorname{sp}(G)\le 5(n-1)/2$.
The source also states: “Note that all conjectures are made for unweighted
digraphs.” The quantified interpretation in
[preregistration #21874](https://github.com/the-omega-institute/trureturing/issues/21874)
is one $C\in\mathbb R$ such that every loopless unweighted digraph of
order $n\ge2$ satisfies $\operatorname{sp}(G)\le n+C$.
That assertion is refuted.

### Statement echo

Short Lean names belong to
`D5.S3.Combinatorics.SpectralGraph.BarrettLaplacianSpreadSlopeRefutation`.
The module has generality `I`.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Unweighted simple digraph on $n$ vertices | `Digraph (Fin n)` | A proposition records each arc; no weights or parallel arcs |
| No loops | `claim` quantifies graphs satisfying the diagonal nonadjacency condition | Opposite arcs are allowed |
| $n\ge2$ | `claim` includes the order bound | Excludes the source's empty restricted sphere at order one |
| $L=D-A$ with out-degree diagonal and $0/1$ adjacency | `laplacian` | The literal real conditional entries and their row sums are displayed |
| $x\perp\mathbf e$, Euclidean unit norm, $x^{\mathsf T}Lx$ | `quadraticValues` | Zero coordinate sum, norm one in `EuclideanSpace`, and the full quadratic expression |
| Minimum $\alpha$ and maximum $\beta$ | `alpha`, `beta` | Infimum and supremum of the same real value set; compactness and nonemptiness give the source extrema for $n\ge2$ |
| $\operatorname{sp}=\beta-\alpha$ | `spread` | The source subtraction order |
| A linear upper bound with slope one | `claim` | One real intercept precedes every order and graph |
| Failure of that universal bound | `result` | The literal conclusion is the negation of the closed `claim` |

The real quadratic form is the source's extrema convention. The literal
adjacency expression stays inside `laplacian`; the private `laplacian_owner`
connects it to the reused natural adjacency definition from
`D5.S1.Dynamics.Symbolic.FiniteGraphEntropy`. No balance or polygonality
hypothesis is added.

## Motivation

An independent-cluster replacement amplifies a positive excess of spread
over order. A fixed finite violation therefore supplies counterexamples to
every intercept, rather than merely to the bound with intercept zero.

## Gap

The source and literature checks recorded on #21874 found no settlement
within their inspected scope. The screen includes the source v1,
Li–Ji arXiv:2411.02440v1 on a balanced upper-bound correction, and
arXiv:2607.03711v1 on an undirected upper bound. The journal text, later
corrigendum contents, full citing-work inventory and complete later-author
coverage were not verified. Literature completeness and priority are
`ASSUMED-UNVERIFIED`; no absence-of-literature theorem is asserted.

## Route

The private `base` is the source Figure 3 graph, with adjacency rows
$00100,10111,11011,00000,00000$.
The private `base_x` and `base_y` certify the zero-sum vectors
$x=(2,26,-26,-1,-1)$ and $y=(0,0,0,1,-1)$, with

$$
\|x\|^2=1358,\quad x^{\mathsf T}Lx=6816,\qquad
\|y\|^2=2,\quad y^{\mathsf T}Ly=0.
$$

The private `blowup` replaces each vertex with $m$ independent vertices,
with all arcs between clusters dictated by the base graph.
The private `sum_cluster` and `lifted_energy` give squared norm multiplied
by $m$ and quadratic energy multiplied by $m^2$.
The private `normalized_mem`, `quadratic_bounded` and `spread_ge_values`
compare the resulting two unit-vector values with the extrema.
Thus the private `blowup_spread` proves, for every positive integer $m$,

$$
\operatorname{sp}(G_m)\ge\frac{3408m}{679}
=5m+\frac{13m}{679}.
$$

The public `result` chooses $m>\max(0,679C/13)$ and contradicts
the putative universal bound at order $5m$.

## Falsifier

The construction would fail if cluster replacement introduced weights or
loops, if either vector were not admissible, if the quadratic scaling
were false, or if the excess did not grow beyond each real intercept.
The proof checks the looplessness, normalization, two quadratic values,
scaling and Archimedean comparison. Its lower bound is sufficient; no
exact eigenvalue identification is a premise.

## Evidence

The public `result` has type literally `¬ claim`, where `claim` is a
closed proposition. The module's admission basis is
`open-problem-resolution (#21874; Refuted)`; its proof shape is `bind-only`
after the consumed helpers are expanded. Its computational utility is
`kind=certified-instance; basis=refutes`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Exact experiment

[Immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/2189938c4555f35b12767dce2ac078784f928114/docs/reports/bcehk-laplspread)
contains `check.py`, SHA-256
`c37f6d846b9c1342f26d3284250e053c90313946f9f50d636cb8483fff3d6366`.
Command:
`python3 /Users/auric/trureturing-experiments/docs/reports/bcehk-laplspread/check.py`,
exit 0, Python 3.14.8 and SymPy 1.14.0. The local script is byte-identical
to that committed blob.
Exact rational arithmetic and root isolation give Figure 3's
$\alpha=0$ and top root in
$[818065/162463,537362/106717]\subset(5.0345,5.0355)$,
so the spread rounds to $5.035$.
The program also checks the two rational-vector certificates and the
independent-cluster identities at $m=1,\ldots,8$.
Those finite experiment checks do not supply the universal quantifier;
the Lean proof supplies it.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| The same unweighted loopless independent-cluster family defeats every real intercept; the excess over order is unbounded | **Proved, kernel-checked:** `blowup_spread` and `result`; the excess lower bound is $13m/679$ |
| Two certified quadratic values and boundedness suffice, without identifying all eigenvalues or the exact spread | **Proved, kernel-checked:** `base_x`, `base_y`, `normalized_mem`, `quadratic_bounded`, `spread_ge_values` and their use in `blowup_spread` |
| The Figure 3 top root lies in $[818065/162463,537362/106717]$ and reproduces spread rounded to $5.035$ | **Computed:** the exact experiment above, exit 0; this is an exact-value experiment, distinct from the kernel-checked lower bound |
| Restricted balanced-graph or polygonal-graph bounds | **Open:** neither restricted assertion is settled by `result` |
| Best universal asymptotic slope and the exact spread of every blowup | **Open:** the lower bound and finite experiment do not establish either optimum or exact family formula |

The failure mechanism is preserved degree imbalance. At base vertex zero,
the displayed adjacency rows give out-degree one and in-degree two;
in the cluster graph these are $m$ and $2m$. This is an explanation proved
in prose directly from the displayed adjacency, rather than an additional
Lean theorem. The family therefore does not negate balanced restrictions.
Polygonal restrictions remain outside the established conclusion.

The nearest surviving source statement is the general
$5(n-1)/2$ upper bound: the certified lower bound does not contradict it.
For $n=5m$ and $m\ge1$, the difference between that upper bound and our
lower bound is $(25/2-3408/679)m-5/2>0$ (elementary rational arithmetic).
The source's balanced results and the balanced corrigendum are separate
claims; no conclusion depending on Conjecture 20 acquires a proof from
the refuted assertion. Any such dependency needs an independent argument.

Literature status: no settlement was found within the inspected scope
described in Gap. Completeness and priority are `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature completeness, priority, the unread journal version and later
corrigendum text remain unverified. The best universal asymptotic slope,
an exact spread formula for every blowup, and restricted balanced or
polygonal bounds remain open. The experiment's exact root enclosure is
computed evidence; the Lean settlement uses the rational lower bound.
