---
slug: hardin-a235290-diagonal-recurrence
bibkey: hardin2014a235290
doi: null
url: https://oeis.org/A235290
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.C
---

# Hardin's eleven-lag recurrence for stress-three square arrays

## Problem

Let $a(n)$ be the number of indexed $(n+1)\times(n+1)$ arrays over
$\{0,1,2,3\}$ in which every contiguous $2\times2$ block has absolute
difference three between its diagonal and antidiagonal sums. The empirical
formula in OEIS A235290, which has offset one, is the following equality
in the integers for every natural number $n\ge12$.

$$
\begin{aligned}
a(n)&=4a(n-1)+23a(n-2)-92a(n-3)-200a(n-4)\\
&\quad+800a(n-5)+820a(n-6)-3280a(n-7)-1584a(n-8)\\
&\quad+6336a(n-9)+1152a(n-10)-4608a(n-11).
\end{aligned}
$$

[Pinned OEIS statement](../Library/Automata/hardin2014a235290.md)

## Motivation

The square count is the diagonal of the stress-three rectangle table
A235301. Each axial recurrence varies one side while the other is
held fixed. A diagonal shift changes both sides at once.

## Gap

The pinned OEIS record gives the signed recurrence as empirical.
The literature and repository search attached to the problem
registration found no exact proof in its stated scope.
[Problem #34377](https://github.com/the-omega-institute/trureturing/issues/34377)

## Route

A normalized boundary-word encoding gives the literal rectangle
counts via a sparse row transfer. For each row mask, a six-state
column computation counts the compatible continuations. This computes
the initial ten-by-ten rectangle of counts. The common order-ten
recurrence along the two axes determines those counts through side
parameter twenty-one.

The residual is the left side of the proposed diagonal recurrence
minus the right side, with each lag acting on both side parameters.
Its formation is a finite linear combination of translated copies
of the rectangle count, so the axial recurrence holds for the residual
in each coordinate. Every entry of the initial ten-by-ten residual
window is zero. Recurrence uniqueness extends the zeros along the first
axis and then along the second. Restricting to equal side parameters
gives the claim.

## Falsifier

A literal square count violating the displayed signed equality at
any natural index at least twelve refutes the claim.

## Evidence

The formal statement is
D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235290DiagonalRecurrence.hardin_a235290.
The count is the integer cast of C 3 3 n n. The lower bound ensures
all eleven lagged side parameters are positive.

[Checked proof evidence](https://github.com/the-omega-institute/trureturing/issues/34377#issuecomment-7182899227)

## Triage

The result applies at every admissible left index. It uses the
listed eleven-lag recurrence and leaves minimal recurrence order open.
