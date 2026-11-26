---
slug: hardin-a235270-diagonal-recurrence
bibkey: hardin2014a235270
doi: null
url: https://oeis.org/A235270
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence.a235280_all_rows_and_columns
---

# Hardin's eleven-lag recurrence for constant-stress squares

## Problem

OEIS A235270 counts indexed $(n+1)\times(n+1)$ arrays over
$\{0,1,2,3,4\}$ in which every contiguous $2\times2$ block has absolute
difference five between its diagonal and antidiagonal sums. Write $A(n)$
for this cardinality, cast to an integer. The entry with offset `1,1`
proposes the following equality for every $n\geq 1$.

$$
\begin{aligned}
A(n+11) &= A(n+10)+23A(n+9)-23A(n+8) \\
 &\quad -200A(n+7)+200A(n+6)+820A(n+5)-820A(n+4) \\
 &\quad -1584A(n+3)+1584A(n+2)+1152A(n+1)-1152A(n).
\end{aligned}
$$

The first full window uses indices 1 through 12.
[Pinned source quotation](../Library/Automata/hardin2014a235270.md)

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Indexed square and alphabet | `C 4 5 n n` counts functions `Fin (n + 1) × Fin (n + 1) → Fin 5` that satisfy the block condition. |
| Every contiguous block has absolute diagonal difference five | The subtype ranges over both upper-left coordinates in `Fin n` and uses `Int.natAbs` of the difference of the two integer sums. |
| Signed eleven-lag identity | `a235270_order11` states the integer equality with the coefficients in the displayed order. |
| Positive source indices | The base index is natural with hypothesis `1 ≤ n`. Both dimensions increase together and the first left-hand index is 12. |

## Motivation

A235270 is the square diagonal of A235280. The fixed-row and fixed-column
identities hold on rectangular slices. The square count requires the
dependence of the profile-size distribution on the width to be tracked
while the height also changes.
[Problem #34348](https://github.com/the-omega-institute/trureturing/issues/34348)

## Gap

Revision 7 marks the eleven-lag recurrence empirical. The bounded
source search recorded in #34348 found no exact proof for all positive
diagonal indices.
[Source search](https://github.com/the-omega-institute/trureturing/issues/34348)

## Route

The fixed-deficit equivalence and rectangular profile sum reduce the
count to alternating products of two complementary row-fiber sizes.
Orient first-cell shifts so that odd-column entries decrease under a
forward shift. Their minimum gives the number of forward steps available
from a row. Counting pairs of anchors with at least prescribed numbers
of available steps reduces to independent column choices. Mixed second
differences of these anchor counts recover the exact pair frequencies.

On the diagonal, a two-index increase multiplies each summand with
positive two-step multiplier by one of $2,3,4,6,8$, or the summand is
constant. The remaining summands vanish. Hence the forward shift $X$
satisfies $(X-1)(X^2-2)(X^2-3)(X^2-4)(X^2-6)(X^2-8)$ on the square
sequence. Expanding yields the eleven signed coefficients.

## Falsifier

A literal square count violating the equality at any positive base
index would refute the published assertion.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235270DiagonalRecurrence.a235270_order11`.
Its Lean axiom closure is `propext`, `Classical.choice` and `Quot.sound`.
An independently stated literal cardinality and the first positive
window instantiate the theorem in Lean.

## Triage

### What the settlement shows

The dependence on both side lengths follows from the exact complementary
fiber-size frequencies. The anchor-count and finite-difference steps
apply to the low-sum rectangle with variable width. The multiplier list
and the signed recurrence apply at deficit three to the stated square
sequence. This supplies the diagonal law for the source entry that
refers to A235280.

## ASSUMED-UNVERIFIED

Global proof priority remains unverified. Minimal order and the
multipliers for other deficits remain open in this settlement.
