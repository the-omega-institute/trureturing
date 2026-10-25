---
slug: gupta-2026-miura-grid-dispersion-inequality-4
bibkey: gupta2026miura
doi: 10.48550/arXiv.2606.22614
url: https://arxiv.org/abs/2606.22614v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.result
---

# Gupta's rectangular-grid dispersion inequality

## Problem

Gupta, *Height functions on the m × n Miura-ori flip graph: degree sequence and diameter*, arXiv:2606.22614v2, Section 4, inequality (4), p. 14, asks for

$\operatorname{disp}(\phi)\le D(m,n)$

for every integer $1$-Lipschitz function on the rectangular grid, realisable or not. Here

$\operatorname{disp}(\phi)=\min_{K\in\mathbb Z}\sum_v|\phi(v)-K|$,

and

$D(m,n)=\min_{K\in\mathbb Z}\sum_{i=1}^m\sum_{j=1}^n|i+j-K|$.

The named external problem and literal conventions are preregistered in [#19839](https://github.com/the-omega-institute/trureturing/issues/19839).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Rectangular grid with horizontal and vertical neighbours | `Fin m × Fin n`, adjacency in `SimpleGraph.pathGraph m □ SimpleGraph.pathGraph n` | Source cell $(i,j)$ is represented by $(i-1,j-1)$. |
| Every integer function, realisable or not | Universal function binder in `claim` | No origami realisability assumption. |
| Adjacent differences at most one | `IsLipschitz` | Literal edge predicate. |
| Minimum over integer centres, each vertex counted once | `disp` | Natural-valued infimum of a nonempty integer-cost range, hence its minimum. |
| One-indexed coordinate sum | `D` | Both zero-based coordinates are incremented by one. |
| Inequality (4) for all positive rectangles | `result : claim` | All natural dimensions are covered; empty rectangles add the zero-cost case. |

The public definitions `IsLipschitz`, `disp`, `D` and `claim` display the source expressions. The existing rectangular graph owner `LeeLiuThreeRowIntegerDomination.grid` is used through the private correspondence `lipschitz_owner`; the public predicate retains its literal graph expression.

## Motivation

The settling declaration is `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.result`. The source's Theorem 4.1 gives the diameter lower bound $D(m,n)$, and Proposition 4.2 bounds the diameter by the largest dispersion of an integer $1$-Lipschitz grid function. Their combination with inequality (4) identifies the diameter for positive rectangles. These two origami reductions are paper results, outside the Lean statement.

## Gap

The pinned source leaves the upper bound for three or more rows open, with finite enumerations through $4\times4$ and $3\times5$. The settlement supplies the universal grid-function inequality. Conjecture 4.6 about abstract $\nu$-chains is a stronger route proposed by the source; the present argument does not establish it.

## Route

Sort rows and then columns. These permutations preserve every sum of a function of the values. Order-statistic monotonicity preserves the comparison between adjacent rows or columns. A missing-level induction shows that sorting a unit-gap integer chain preserves unit gaps: a gap of at least two would split the original chain into two nonempty threshold classes, although no adjacent step could cross between them.

Write $F$ for the rearranged function and $A(i,j)=i+j$. Both $F$ and $R=A-F$ are increasing. For the uniform average $E$, put $X=F-EF$, $Y=A-EA$ and $s=\operatorname{sgn}(X)$. The scalar subgradient inequality gives

$\sum|Y|\ge\sum|X|+\sum s(Y-X)$.

FKG for increasing functions on the product of chains implies $\operatorname{Cov}(s,R)\ge0$. Since $Y-X=R-ER$, the last sum is nonnegative. Thus the centred absolute deviation of $F$ is at most that of $A$.

An integer-valued finite sample has an integer centre no worse than any rational centre: between consecutive integers the cost is affine, so one endpoint has no larger cost. Reflection of both grid coordinates pairs the values of $A$ around $(m+n+2)/2$; the triangle inequality shows that this centre minimizes its rational cost. Combining these estimates proves inequality (4). Empty rectangles have zero dispersion.

## Falsifier

A counterexample would consist of dimensions, an integer grid function satisfying every unit edge bound, and an integer-centre minimum exceeding $D(m,n)$. Losing an edge hypothesis, a vertex multiplicity, an integer-centre restriction or either coordinate offset would invalidate fidelity. A finite experiment cannot replace the universally quantified proof.

## Evidence

Kernel-checked settlement: `D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion.result`, with the full `claim` proposition. Its only public theorem is this result; the supporting lemmas are private. The Blueprint displays all four public definition bodies and the full settling proposition.

Finite validation uses [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/53ef35ac1f4fbc9b4d0b6d339c778d89cec82b8d/docs/reports/gupta-2026-miura-grid-dispersion-inequality-4), script `check.py`, SHA-256 `872ef5b3868b12abce34bfee74f7972bbed0036012ed4288f9002fbddf2f7726`. Validation command for the immutable script: `/opt/homebrew/bin/python3 /Users/auric/.sshx/b571e465e1e701664d0c74f6/attempt-1/check.py`, exit 0. The tested scope and results are listed under Triage.

Escape audit unfinished: [#21178](https://github.com/the-omega-institute/trureturing/issues/21178), for the settling `result`. The dependent infinite family lacks compiled whole-source reconstruction, equivalence, actual-positive, intervention/sensitivity and observational-dependence evidence. No Reg registration is delivered or claimed validated.

## Triage

### What the settlement shows

- **Proved, kernel-checked:** the exact universally quantified GM-4 binding claim, by `GuptaMiuraGridDispersion.result`, for all natural dimensions and all integer functions satisfying only the grid-edge bounds.
- **Mechanism, proved in prose above and implemented in private lemmas:** rearrangement makes both $F$ and $A-F$ increasing; centred FKG compares their absolute deviations. This is the comparison for the absolute-value cost; no general convex-order theorem is asserted. Conjecture 4.6 is not a premise.
- **Sharpness, proved in prose:** the source function $\phi(i,j)=i+j$ changes by exactly one along each edge. Its centre-cost minimum is the definition of $D(m,n)$, so equality is attained. This explanation is not a separate public Lean theorem.
- **Consequence, proved in prose using the paper's Theorem 4.1 and Proposition 4.2:** for positive rectangles, the lower and upper bounds coincide, giving $\operatorname{diam}\operatorname{OFG}(M_{m,n})=D(m,n)$. This settles the rectangular Miura diameter question of Section 5 subject to those paper reductions; the reductions and flip graph itself are not formalized here.
- **Open:** Gupta Conjecture 4.6 for all abstract $\nu$-chains. The grid rearrangement argument supplies no theorem about all such chains.
- **Open:** broader origami flip-graph diameter questions outside rectangular Miura, including the remaining scope of Christensen et al., arXiv:2506.19700v3, Section 6.

### Finite validation (computed)

All entries use the single experiment command, exit code and script hash in Evidence. They are finite computations, independent of the universal kernel-checked theorem.

The script checks $D(2,n)=\lceil n^2/2\rceil$ for $2\le n\le11$ and $D(m,m)=(m^3-m)/3$ for $1\le m\le8$; every comparison passes. No general closed-form identity is claimed as a Lean theorem here.

| Enumerated family | Grid | Number of functions | Maximum dispersion $=D(m,n)$ |
| --- | --- | --- | --- |
| All integer $1$-Lipschitz functions normalized at the first cell | $2\times3$ | 121 | 5 |
| Same | $2\times4$ | 771 | 8 |
| Same | $2\times5$ | 4913 | 13 |
| Same | $2\times6$ | 31307 | 18 |
| Same | $2\times7$ | 199497 | 25 |
| Same | $3\times3$ | 1665 | 8 |
| Same | $3\times4$ | 22979 | 14 |
| Same | $3\times5$ | 317259 | 20 |
| Same | $4\times4$ | 690437 | 20 |
| Increasing functions with increments zero or one, normalized at the first cell | $3\times6$ | 7782 | 29 |
| Same | $4\times5$ | 18150 | 30 |
| Same | $5\times5$ | 193662 | 40 |

### Literature status

The source/literature screen recorded in #19839 covers source versions v1/v2, Gupta's degree-enumeration sequel arXiv:2607.05567v3, Christensen et al. arXiv:2506.19700v3 Section 6, OpenAlex citing works, MathDB's slowest-chain entry and the formal-conjectures corpus. Within that searched scope it records no earlier settlement. These are attributed literature readings, not kernel proofs. Completeness is **ASSUMED-UNVERIFIED**.

## ASSUMED-UNVERIFIED

The literature screen is not exhaustive. The origami distance and lower-bound reductions remain external mathematical inputs to the diameter interpretation. No uniform abstract-chain or nonrectangular origami conclusion follows from the delivered theorem. Escape registration remains unfinished under #21178.
