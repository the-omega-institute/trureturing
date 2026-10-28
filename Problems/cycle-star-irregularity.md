---
slug: cycle-star-irregularity
bibkey: salmanageshnarahari2024cyclestar
doi: 10.22199/issn.0717-6279-5801
url: https://arxiv.org/abs/2405.12263v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.result
---

# Edge irregularity strength of cycle-star graphs

## Problem

Salma–Nagesh–Narahari, *On edge irregularity strength of cycle-star graphs*,
Proyecciones 43(3), 725–741, arXiv:2405.12263v1, Conjecture 3.1, states:

> Let $G=CS_{k,n-k}$ be a cycle-star graph. For $k\geq8$ and $n-k\geq1$,
> $$es(G):=\begin{cases}\lceil(n+1)/2\rceil&\text{for }k+1\leq n\leq2k-4,\\n-k+2&\text{for }n\geq2k-3.\end{cases}$$

The graph consists of a cycle of length $k$ with $n-k$ leaves appended to
one vertex. A vertex labeling takes values in $\{1,\ldots,K\}$ and may repeat
labels; different unordered edges must have different endpoint sums.
The strength is the least positive feasible bound and includes attainment.
The source and binding conventions are in [#22868](https://github.com/the-omega-institute/trureturing/issues/22868).
The source note is [Salma–Nagesh–Narahari](../Library/FiniteGeometry/salmanageshnarahari2024cyclestar.md).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every $k\geq8$ and $n-k\geq1$ | `claim` quantifies natural $k,n$ with both hypotheses | Exact source domain |
| Vertices $v,v_i$, $1\leq i\leq n-1$ | `cycleStar` has carrier `Fin n`; zero represents $v$ | Exact indexing |
| Leaf edges, both cycle-closing edges, consecutive internal edges | `cycleStar` uses the three source index ranges inside `SimpleGraph.fromRel` | Undirected, loopless edge set |
| Labels $1$ through $K$, repetitions allowed | `IsKLabeling` | No vertex-injectivity assumption |
| Edge weights are endpoint sums; different edges have different weights | `edgeWeight`, `IsEdgeIrregularLabeling`, unordered equality in `Sym2` | Reversing orientation preserves the edge |
| Minimum feasible label bound | `IsEdgeIrregularityStrength` uses `IsLeast` on positive feasible bounds | Attainment and comparison with every feasible bound |
| $k+1\leq n\leq2k-4$: $\lceil(n+1)/2\rceil$ | First conjunct of `claim`, natural division $(n+2)/2$ | Same ceiling |
| $n\geq2k-3$: $n-k+2$ | Second conjunct of `claim` | Exact source value |

No hypothesis assumes a labeling exists. Positivity of feasible bounds is
the source's label-bound convention, rather than an additional graph
hypothesis. Under the source domain, the two ranges exhaust all parameters.

## Motivation

The paper establishes the short-cycle cases and asks for the uniform
formula at every remaining cycle length. The result supplies that formula
without a bound on either the cycle length or the number of leaves.

## Gap

Finite labelings alone do not establish an unbounded minimum theorem.
The required assertion combines a uniform construction with lower bounds
against every feasible labeling. Source openness is established only in
the searched and read literature scope; completeness remains
ASSUMED-UNVERIFIED.

## Route

Put $m=n-k$ and $K=\max\{m+2,\lceil(m+k+1)/2\rceil\}$. Distinct edge sums
lie in $[2,2L]$, and the $m+2$ neighbors of the common vertex have distinct
labels in any feasible $L$-labeling. The private `labeling_lower` proves
$m+2\leq L$ and $\lceil(m+k+1)/2\rceil\leq L$ using finite injections.

For the upper bound, label the common vertex $K$. Along the remaining
cycle path use $y_j=\lceil j/2\rceil$, with an additional one exactly when
$K\leq k-2$, $j>K$ and $j-K$ is odd. In the smaller-bound branch, consecutive
sums are $j+1$ before the threshold and $j+2$ afterwards. The omitted sum
$K+1$ closes one end of the cycle, and the other closing sum exceeds $k$.
Choose leaf labels above $k-K$, skipping the far endpoint label through
`Fin.succAbove`. Their weights are distinct and exceed $k$, and none equals
the far closing sum. In the other branch, internal sums are at most $K$
and the closing and leaf sums exceed $K$.

The private `labeling_upper` constructs this bounded labeling and proves
all edge-weight separations. `strength_of_bounds` combines it with the
lower bounds; `result` specializes the maximum to the two source ranges.

## Falsifier

A natural pair $k,n$ with $k\geq8$ and $n-k\geq1$ for which the specified
bound is unattainable, or a feasible labeling with a smaller positive
bound. The edge set, label convention and unordered-edge equality are fixed
as in the statement echo.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.result`.
It proves `claim`, including both source ranges, existence and minimality.
Its module has `generality: G`, `utility: none` and
`admission_basis: open-problem-resolution (#22868; Proved)`.
The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}.

### Finite computation

The independent finite checker is in
[trureturing-experiments at bca5cba400e427feb7569b21bc7c0ae894a85c1a](https://github.com/the-omega-institute/trureturing-experiments/tree/bca5cba400e427feb7569b21bc7c0ae894a85c1a/docs/reports/salma-nagesh-narahari-cycle-star-irregularity),
path `docs/reports/salma-nagesh-narahari-cycle-star-irregularity/check.py`.
The committed blob is verified with `git cat-file -e`; its SHA-256 is
`efc70ce44faa45b882da37acc809ea2a4bfd4d6a8421b1482db217f4fdaad226`.
Command: `python3 /Users/auric/.sshx/c9999353056a46a29ecd5b2e/attempt-1/checker.py`,
using the byte-identical pinned blob; exit 0, `ALL_CHECKS_OK`.

The tested scope is: 40 source Theorem 3.2 labelings at $k=3$, $1\leq m\leq40$;
60 source/cyclic edge-set isomorphisms and 60 exact minima at
$3\leq k\leq12$, $1\leq m\leq6$; 12,560 constructed labelings at
$4\leq k\leq160$, $1\leq m\leq80$, with 3,320 large-bound and 9,240
small-bound branches and their inventories; 12,240 source-piecewise
identities at $8\leq k\leq160$, $1\leq m\leq80$.
These computations are finite evidence and are not used in the Lean proof.

## Triage

| Item | Status and evidence |
| --- | --- |
| Exact source quantifiers $k\geq8$, $n-k\geq1$: both displayed strengths attained and minimal | **Proved, kernel-checked:** public `result` |
| Missing-sum construction and skip map separate internal path weights, both closing weights and all leaf weights | **Proved, kernel-checked:** private `y_sum`, `path_sum`, `neighbor_inj`, `hub_path_disjoint` and `arc_weight_inj`, consumed by `labeling_upper` |
| Upper-bound helper for $k\geq4$, $m\geq1$, $m+2\leq K$, $m+k+1\leq2K$ | **Proved, kernel-checked:** private `labeling_upper`; no separate extension settling theorem |
| Pinned finite checker | **Computed:** the experiment entry gives the script, immutable revision, SHA-256, command, exit 0 and exact finite scope |
| Other graph operations, products and powers | **Open:** no such conclusion is asserted |
| Global literature completeness and full screens of inaccessible primary papers | **Open:** literature completeness is ASSUMED-UNVERIFIED; access limits are listed below |

### What the settlement shows

The decisive construction separates four edge classes by an exact
missing-sum inventory and an explicit skipped leaf label. It yields a
uniform attained upper bound, while the degree and edge-count injections
force the matching minimum. The public theorem settles precisely the
source's $k\geq8$ assertion. Its consumed upper-bound helper also works for
$k\geq4$, $m\geq1$ with the two stated inequalities on $K$; that helper is
not an additional public settlement. The lower bounds show sharpness.
The source's established short-cycle results are compatible with this
construction; its $k=3$ formula is only a finite-check fidelity target here.
The source ends with the conjecture, and this delivery asserts no further
consequence for other graph operations, products or powers.

## ASSUMED-UNVERIFIED

The literature screen in #22868 found no complete settlement in the
searched and read scope. The published $m=1$ kite specialization is
literature-attested; the unbounded construction is a suspected-new
synthesis, without an exhaustive priority claim. Full primary theorem
screens remain unverified for DOI 10.1007/s44427-026-00036-5,
10.1142/S1793830925501423, 10.1016/j.amc.2014.06.028 and
10.37256/cm.6120255957. Citation enumeration and general-web access were
incomplete. These are literature boundaries, not Lean proof premises.

The four-slot escape audit is unfinished for the sole public theorem,
`D5.S3.Combinatorics.EdgeLabeling.CycleStarIrregularity.result`:
[issue #23027](https://github.com/the-omega-institute/trureturing/issues/23027).
No Reg registration is retained. The exact reconstruction, enrolled
readout, variation, sensitivity and observational-dependence evidence
for its guarded leastness family are missing; no `declared_validated`
registration is claimed.
