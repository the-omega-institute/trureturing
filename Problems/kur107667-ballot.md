---
slug: kur107667-ballot
bibkey: kurkov2026a107667
doi: null
url: https://oeis.org/history/view?seq=A107667&v=25
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.result
---

# Kurkov's weighted-ballot formula for OEIS A107667

## Problem

Mikhail Kurkov's FORMULA conjecture in Paul D. Hanna's [OEIS A107667, approved revision 25](https://oeis.org/history/view?seq=A107667&v=25) asserts
$T(n+m,m)=(n+m+1)P(n+1,n+1,m)$ for all $n,m\in\mathbb N$.
The preregistration is [#21639](https://github.com/the-omega-institute/trureturing/issues/21639).
The source is OEIS-only, with no claim-source DOI or arXiv identifier identified.

The source NAME defines a lower triangular matrix by $T=D+\operatorname{SHIFT\_LEFT}(T^2)$ with diagonal $1,2,3,\ldots$.
Thus $T(a,b)=0$ for $a<b$, $T(a,a)=a+1$, and
$T(a,b)=\sum_{j=b+1}^{a}T(a,j)T(j,b+1)$ for $b<a$.
Kurkov's three-argument table satisfies $P(r,1,m)=1$ for $r\ge1$,
$P(r,k,m)=P(r-1,k,m)+(r+m)P(r,k-1,m)$ for $1<k<r$, and
$P(r,r,m)=(r+m)P(r,r-1,m)$ for $r\ge2$.
Values outside $r\ge k\ge1$ are unrestricted.
This table is distinct from the source's earlier two-argument conjugating matrix also called $P$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Lower triangular $T=D+\operatorname{SHIFT\_LEFT}(T^2)$, diagonal $1,2,3,\ldots$ | `IsSourceTriangle` | All three literal recurrence clauses, with zero-based indices and a finite interval sum. |
| Base, interior and diagonal rules for three-argument $P$ | `IsPTable` | Base includes $P(1,1,m)=1$; diagonal starts at row $2$. |
| The two-parameter identity | `claim`, `result` | Every natural-valued pair of tables satisfying those rules, every $n,m\ge0$, and the full displayed equality. |

The additional table binders and recurrence hypotheses express the source definitions; no path formula or first-return identity is assumed.

## Motivation

The recurrence has a parameter-sensitive first-return convolution. Its diagonal specialization matches the nonlinear triangle recurrence after reindexing by $j=m+i+1$.

## Gap

The source revision and inspected literature recorded in #21639 do not supply a settlement of the full two-parameter assertion. The screen includes OEIS cross-references, identifier and author searches, and selected weighted-path and automata literature. Citation services returned HTTP 429, and identified publisher sources were unread or incompletely readable. Completeness is `ASSUMED-UNVERIFIED`; no exhaustive priority claim follows.

## Route

For the proof's zero extension, write
$B_m(x,y)=\mathbf 1_{y\le x}P(x+1,y+1,m)$.
The Lean source uses `Set.indicator` on `Set.Iic`, without a separate definition of $B$.
The private `b_zero`, `b_above` and `b_step` express its base value, upper-triangle zero rule and last-step recurrence.
The private `first_return` proves, for every $y\le x$,

$$
B_m(x+1,y+1)=B_{m+1}(x,y+1)+
\sum_{i=0}^{y}(m+i+2)B_{m+1}(i,i)B_{m+i+1}(x-i,y-i).
$$

Nested induction on $x,y$ proves this identity from the source rules. Its diagonal specialization, followed by strong induction on $n$ and the reindexing $j=m+i+1$, proves `result`.
No separate path-set bijection is formalized.

## Falsifier

A change to either recurrence, the diagonal starting index, the parameter shifts or the conclusion changes the assertion. A finite check cannot establish the all-index result. A previously published dominating theorem would limit the novelty claim while preserving the kernel-checked statement.

## Evidence

`D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.result` proves `claim`.
The module has `generality: I`, `utility: none` and `admission_basis: open-problem-resolution (#21639; Proved)`.
Its imports are Mathlib modules; there is no D5 prerequisite, atom or cover.

The four-slot escape audit for the public `result` is unfinished under [#21710](https://github.com/the-omega-institute/trureturing/issues/21710).
Missing evidence comprises the full infinite-table source realization and reconstruction bridge, lawful enrolled readout, source selection, and whole-family variation, sensitivity and observational dependence. No `declared_validated` registration is asserted.

### Experiment

The supplementary checker is in [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/c6dfab1668384a051dd637ebe1266fd2dcc663fa/docs/reports/kurkov-a107667-ballot), commit `c6dfab1668384a051dd637ebe1266fd2dcc663fa`.
Command from that revision's repository root: `python3 docs/reports/kurkov-a107667-ballot/check.py`; exit $0$.
Script SHA-256: `06b50553d410615faa69c532db989059c5d256c2b2f83f5edaa3154e39e7f3d8`.
The final check is `ALL_CHECKS_OK`.
It verifies $36$ displayed $T$ entries, $28$ displayed $T^2$ entries, $136$ diagonalization entries through row $15$, all $861$ identity entries $0\le b\le a\le40$, $12341$ P/path entries for $0\le m\le40$ and $0\le y\le x\le40-m$, $820$ diagonal first-return identities for $0\le m\le39$ and $1\le d\le40-m$, and $54$ direct path enumerations for $0\le m\le5$, $0\le d\le8$.
These finite exact readings are supplementary evidence, not the universal proof.

## Triage

Tier $1$; resolution `Proved`.

### What the settlement shows

| Target item | Status and evidence |
| --- | --- |
| Exact conjecture for every nonnegative $n,m$ and every pair of source tables, including $n=0$ and $m=0$. | **Proved, kernel-checked:** `result`, with the complete `claim`. |
| Stronger off-diagonal first-return factorization for every $y\le x$. | **Proved, kernel-checked:** private `first_return`, with the full identity displayed in Route. |
| The first-column identity at $m=0$. | **Proved in prose from `result`:** substitute $m=0$ in its universal conclusion and simplify $n+0=n$, obtaining $T(n,0)=(n+1)P(n+1,n+1,0)$. No separate declaration is delivered. |
| Supplementary $861$ identity entries, $12341$ P/path entries, $820$ first-return identities and $54$ direct enumerations. | **Computed:** the pinned checker, command, exit $0$, SHA-256 and exact tested scope in Evidence; `ALL_CHECKS_OK`. |
| A separately formalized path-set bijection, arbitrary weight-sequence extension and links to canonical automata/state-graph counts. | **Open:** neither the compiled result nor the finite checker proves these extensions. |

The decisive mechanism is the shifted-parameter convolution, which applies off the diagonal as well as on it. The source's first-column conjectural specialization follows. Other formulas, asymptotics and automata interpretations in related entries retain their separate proof obligations; no dependency of another published theorem on this conjecture is asserted.

## ASSUMED-UNVERIFIED

Literature completeness, priority and the absence of a dominating result in unread sources remain unverified. The preregistration identifies the citation-service failures and unread works. The escape registration is unfinished under #21710; mathematical verification does not supply that registration.
