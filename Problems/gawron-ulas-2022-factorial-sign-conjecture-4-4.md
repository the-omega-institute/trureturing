---
slug: gawron-ulas-2022-factorial-sign-conjecture-4-4
bibkey: gawronulas2022partitions
doi: 10.1007/s11139-022-00602-3
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.result
url: https://arxiv.org/abs/2202.05221v1
---

## Problem

Gawron and Ulas, “Signs behaviour of sums of weighted numbers of partitions”,
arXiv:2202.05221v1, Conjecture 4.4, p. 11, asks for two eventual sign inequalities
for $U_m=\{i!:1\le i\le m\}$, $m\ge2$. With $c_A(i,n)$ counting unordered
partitions of $n$ into exactly $i$ positive parts from $A$, put
$S_{A,k}(n)=\sum_{i=0}^n(-1)^i i^k c_A(i,n)$.

The first assertion is $(-1)^{\lfloor(n+1)/2\rfloor}S_{U_m,k}(n)\ge0$
for every sufficiently large $n$ when $0\le k\le m-2$.
The second assertion is $(-1)^nS_{U_m,k}(n)\ge0$ for every sufficiently large
$n$ when $k\ge m-1$. Each threshold may depend on $m$ and $k$.
The settlement is **Refuted**, specifically for the v1 statement.
The preregistration is [#19687](https://github.com/the-omega-institute/trureturing/issues/19687).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Unordered positive-part partitions with exactly $i$ parts in $A$ | `c` filters `Nat.Partition n` by part membership and `Multiset.card` | Literal count; allowing zero in $A$ adds no partition |
| Sum from $0$ through $n$ with weight $(-1)^i i^k$ | `S` uses `Finset.range (n+1)` and integer casts | Both endpoints; $0^0=1$ |
| $U_m=\{i!:1\le i\le m\}$ | `U` uses the existential factorial membership condition | Literal set |
| Every $m\ge2$, every $k\le m-2$, eventual floor-exponent inequality | First conjunct of `claim` | Natural division is the floor; no least-period assertion |
| Every $m\ge2$, every $k\ge m-1$, eventual alternating inequality | Second conjunct of `claim` | Independent existential threshold for each pair |
| Negation of the whole conjecture | `result : ¬ claim` | Contradicts the second conjunct at $m=3,k=2$ |

## Motivation

The frozen declaration
`D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.result`
settles the named source proposition. The source note is
`Library/RecurrenceComposition/gawronulas2022partitions.md`.

## Gap

The second assertion predicts a uniform tail of nonnegative alternating signs.
An unbounded family of even arguments with negative sums rules out every threshold;
a finite list of negative values alone would not do so.

## Route

The module uses the literal source definitions. Private `S_coordinates`
regroups partitions by multiplicities $y$ of 2 and $z$ of 6. The remaining
multiplicity is $n-2y-6z$, and the number of parts is $n-y-5z$.
Private `alternating_quadratic` and `outer_alternating` apply
`Finset.sum_range_sub'` to polynomial telescopes. Private `outer_ordinary`
applies `sum_range_pow` at exponents 1 and 2. Private `cubic` combines them:

$$3S_{U_3,2}(12r+2)=-52r^3+69r^2+82r+9\qquad(r\in\mathbb N).$$

Private `negative_family` substitutes $r=s+3$ to obtain
$S_{U_3,2}(12s+38)<0$ for every natural $s$.
For every proposed threshold $N$, `result` uses the even argument $12N+38\ge N$.
All proof shapes are bind-only after expansion; the admission basis is
`open-problem-resolution (#19687; Refuted)`.

## Falsifier

The refutation would not address the source if the count, exponent-zero
convention, factorial set, or eventual quantifiers differed from the quoted
v1 definitions. These are explicit in the statement echo. The final journal
wording has not been verified, so no identity of the journal and v1 statements
is asserted.

## Evidence

The Lean module proves `result` with no hypotheses; its private lemmas prove
the cubic identity and the unbounded negative family above.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Exact integer checks](https://github.com/the-omega-institute/trureturing-experiments/tree/2ebc8fc7ee9c594b94d9ca0972a2f546e9830c89/docs/reports/gawron-ulas-2022-factorial-sign-conjecture-4-4).
Command: `python3 /Users/auric/trureturing-experiments/docs/reports/gawron-ulas-2022-factorial-sign-conjecture-4-4/check.py`.
Exit code: 0.
Script SHA-256: `75031151f4d857abf79ff4e0e0664dce4451b53d14a92b92df328fd9ea14206c`.
The source generating functions at $k=0,1$ agree with the partition counts
for $0\le n<80$; the $k=1$ period-four strict inequality holds for $8\le n<80$.
The cubic is checked for $0\le r\le40$, with
$S(38)=-176$, $S(50)=-629$, and $S(62)=-1452$.
For each $(k,b)$ in
$(2,400),(3,400),(4,800),(5,1000),(6,1500),(7,3000),(8,6000)$,
the period-four strict inequality holds for all $b\le n\le b+7$;
the alternating sign inequality is violated at four of those eight arguments.
These finite readings do not prove a uniform eventual statement.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| v1 Conjecture 4.4 at $m=3,k=2$ | **Proved refuted in Lean:** public `result`, via private `negative_family` |
| Exact all-$r$ cubic identity | **Proved in Lean:** private `cubic` |
| Failure mechanism | **Proved in Lean:** private `negative_family` gives negative sums on the unbounded even progression $12s+38$; `result` defeats every threshold |
| Source observation for $A=\{1,2,6\}$, $k\ge2$ | **Proved false in Lean at $k=2$:** the same `negative_family`; no statement for every $k$ is claimed |
| Generating functions and small-parameter values | **Computed:** experiment scope and readings in Evidence |
| Large-$n$ sign windows for $2\le k\le8$ | **Computed:** the seven eight-point windows in Evidence; no claim for untested $n$ |
| First assertion of Conjecture 4.4 | **Open:** this proof does not decide it |
| Eventual period-four signs for every $k$ or larger factorial sets | **Open:** the windows and this single-parameter proof do not establish a uniform extension |
| Pole-order explanation | **Open:** the proposed coefficient representation uses $(t\partial_t)^k\prod_{a\in A}(1-tx^a)^{-1}$ at $t=-1$; the proposed dominance of poles at $\pm i$ over the pole at $-1$ and the crossover explanation are not proved by this module or experiment |
| Corrected assertion for every $m\ge3$ and every $k$ | **Open:** eventual period-four signs are a candidate, not a theorem here |
| Consequences for source results using the conjecture | **Open:** no dependence of the journal results on this conjecture has been verified; no other source theorem is declared false |
| Novelty and published-version literature check | **ASSUMED-UNVERIFIED:** no first-refutation or exhaustive-search claim; the final journal text is not verified |
| Independent proof review and canonical integration | Canonical Lean and Scribe are supplied; independent proof review is **open**, represented by the Draft PR review standing |

## ASSUMED-UNVERIFIED

The literature screen recorded in #19687 covers the arXiv v1, a subscription
journal preview, MathDB, the formal-conjectures archive and the later papers
arXiv:2401.17386 and arXiv:2308.07698. These are source-check readings reported
by the search seat and orchestrator. Literature completeness and publication
priority remain ASSUMED-UNVERIFIED. The publisher text may revise Conjecture 4.4;
the settled proposition is the quoted arXiv v1 statement.
