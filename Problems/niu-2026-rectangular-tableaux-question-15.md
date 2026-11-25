---
slug: niu-2026-rectangular-tableaux-question-15
bibkey: niu2026firstdescent
doi: 10.48550/arXiv.2610.03038
url: https://arxiv.org/abs/2610.03038v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/NiuQ15.rectangleQuestion15
---

# Niu's Question 15 on first descents in rectangular tableaux

## Problem

Fix an integer $K\ge 2$. For each width $n>0$, choose a standard Young tableau
$T$ of the $K$ by $n$ rectangle uniformly, with one-based entries. The first
descent is $D_n=T(2,1)-1$. Question 15 asks for the limiting first-descent law
and the parity constant for a fixed row count. Here parity refers to the
one-based entry $T(2,1)$ being odd. [Question 15](https://arxiv.org/html/2610.03038v1#Thmtheorem15)

The exact Lean proposition is `NiuQ15.Question15`. For every natural $k$, it
sets $K=k+2$ and requires the following four clauses.

| Clause | Value or condition |
| --- | --- |
| Survival limit for every natural $r$ | $\lim_{n\to\infty}\Pr(D_n\ge r)=S_K(r)=\binom{r+K-1}{K-1}/K^r$ |
| Point limit for every natural $r$ | $\lim_{n\to\infty}\Pr(D_n=r)=p_K(r)=r\binom{r+K-1}{K-2}/K^{r+1}$ |
| Normalization | $\sum_{r\ge 0}p_K(r)=1$ |
| Odd-entry limit | $\lim_{n\to\infty}\Pr(T(2,1)\text{ is odd})=(K/(K+1))^K$ |

The natural-width sequences in Lean use a total extension at $n=0$.
The three limits are along `atTop` in width for each fixed $K$. The point
mass at $r=0$ is zero, so normalization also holds over positive $r$.

## Motivation

The source gives the three-row law and its odd-entry constant $27/64$.
The rectangular question asks for the dependence on the fixed number
of rows. [Theorem 4](https://arxiv.org/html/2610.03038v1#Thmtheorem4)
[Problem scope and literature screen](https://github.com/the-omega-institute/trureturing/issues/32036)

## Gap

The prefix rotation reduces the finite survival probability to a ratio
of straight-shape counts. Evaluating that ratio gives the fixed-threshold
limit. The parity event sums over a range of descents that grows with width,
so pointwise limits require a summable bound to justify this passage.

## Route

Partition the tableaux of a nonempty straight shape by the removable
row end containing the largest label. Removal and reinsertion identify
each part with the tableaux of the smaller shape. The shifted
Vandermonde factorial expression satisfies the same sum recurrence
by interpolation at the shifted row lengths. Its empty-shape value is
one. Induction on the number of cells identifies it with the tableau
count for straight shapes with at least two rows, allowing trailing
zero lengths.

For $0\le r\le n$ at positive width, survival means that the first
$r$ labels occupy the top-row prefix. Delete that prefix, rotate the
complement by $180$ degrees, and reverse the remaining labels. This
gives a bijection with tableaux of the shape $(n^{K-1},n-r)$.
The resulting survival probability is
$\binom{r+K-1}{K-1}(n)_{\underline r}/(Kn)_{\underline r}$, where
$(a)_{\underline r}$ is the descending factorial. For $r>n$ the event
is empty. For each fixed $r$, the ratio tends to $K^{-r}$.
Adjacent differences give the masses, and telescoping gives their
normalization. The even-descent sum equals the alternating sum of
survival probabilities. A common geometric majorant permits the
limit inside this sum, whose binomial series evaluates to
$(K/(K+1))^K$.

## Falsifier

A different limit for any fixed $K\ge 2$ and natural threshold, a
failure of mass normalization, or a different odd-entry limit for
any such $K$ would contradict the corresponding clause. A failure
of the shortened-shape identity at a positive width and $r\le n$
would contradict the finite count used by the proof.

## Evidence

The settling theorem is `NiuQ15.rectangleQuestion15 : NiuQ15.Question15`.
Its axiom closure is `Classical.choice`, `Quot.sound`, and `propext`.

The two source-bound Reg modules record five validated source-equivalence
bindings. The `NiuQ15` Reg module covers `rectangleQuestion15`,
`exactRectangleTailCount`, and `card_standardTableau_eq_shiftedCount`.
The `NiuTableauCount` Reg module covers `shiftedCount_empty` and
`shiftedCount_recurrence`. The continuation of each binding is open.
[Rectangle Reg source](../Reg/D5/S3/Combinatorics/Partitions/NiuQ15.lean)
[Count Reg source](../Reg/D5/S3/Combinatorics/Partitions/NiuTableauCount.lean)

Sixteen supporting theorems in the scoped audit have unfinished
registrations. The tableau results need a dependent readout preserving the
shape, tableau, and event or deletion data. The analytic results need a
readout on the original sequences and indices that preserves the exact
premises. Both groups need evidence of sensitivity to intervention and
dependence on the actual observation.
[Supporting registration disclosure](https://github.com/the-omega-institute/trureturing/issues/32036#issuecomment-7031770072)

## Triage

### What the settlement shows

The GIDs in the table are relative to `D5/S3/Combinatorics/Partitions/`.

| Result | Proved by | Scope |
| --- | --- | --- |
| One-cell deletion recurrence | `NiuTableauCount.shiftedCount_recurrence` and `NiuQ15Tableaux.card_standardTableau_eq_sum` | The count recurses over removable row ends of nonempty straight shapes. The shifted formula is proved for antitone row lengths with at least two rows. |
| Survival bijection and count | `NiuQ15Tableaux.card_rectangle_tail`, `NiuQ15Tableaux.card_rectangle_tail_of_width_lt`, and `NiuQ15.exactRectangleTailCount` | For $K\ge 2$ and $n>0$, the bijection and factorial identity apply when $r\le n$. The above-width survival event is empty. |
| Geometric domination and parity | `NiuQ15Analytic.tendsto_alternating_finiteTail` | The majorant is $1$ at $r=0$ and $(3/4)^{r-1}$ at $r\ge 1$, uniformly over widths and $K\ge 2$. It justifies the limit in width for each fixed $K$. |
| All four clauses | `NiuQ15.rectangleQuestion15` | The result includes the source's three-row law as a specialization. The limiting law and parity concern fixed row counts. |

Question 13 of the same paper concerns the order of a three-row recurrence
and remains open in this settlement.
[Question 13](https://github.com/the-omega-institute/trureturing/issues/26626)

## ASSUMED-UNVERIFIED

The literature screen in the linked issue is bounded. Publication priority
and exhaustive source coverage remain unverified.
[Recorded search scope](https://github.com/the-omega-institute/trureturing/issues/32036)
