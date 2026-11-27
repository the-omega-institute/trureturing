---
slug: hardin-a235280-common-recurrence
bibkey: hardin2014a235280
doi: null
url: https://oeis.org/A235280
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence.a235280_all_rows_and_columns
---

# Hardin's common order-9 recurrence for A235280

## Problem

Let $T(n,k)$ count the literal indexed $(n+1)×(k+1)$ grids over $0,\ldots,4$ for which every contiguous $2×2$ block has absolute diagonal difference 5. The table has offset `1,1`. Its FORMULA proposes a common recurrence for all rows and columns. The empirical coefficient row is independently published for column 9 as A235279. [Table scope](../Library/Automata/hardin2014a235280.md) · [Coefficient row](../Library/Automata/hardin2014a235279.md) · [#34321](https://github.com/the-omega-institute/trureturing/issues/34321)

With $(c_1,\ldots,c_{9})=(1,15,-15,-80,80,180,-180,-144,144)$, both identities hold for every $n,k\geq1$:

$$
T(n+9,k)=\sum_{j=1}^{9} c_j T(n+9-j,k),
\qquad
T(n,k+9)=\sum_{j=1}^{9} c_j T(n,k+9-j).
$$

In Lean, `C 4 5 n k` counts the literal legal subtype. The two equations of `a235280_all_rows_and_columns` use integer casts and all signed terms in published lag order. The first eligible varying index is 10 in each direction. The scope is the common axis recurrence, including a fixed index of one. Slice minimal order and diagonal recurrences are separate questions.

## Motivation

The A235280 FORMULA proposes the same signed law in both table directions. This tests the full rectangle family, including the first row and first column.

## Gap

The exact scope requires every positive pair of indices. The empirical coefficient row at A235279 fixes one column. The nearby A235289 theorem uses four symbols and stress four.

## Route

At deficit 3, the checkerboard transform, uniformity of adjacent block sums, global complementation and restriction to $0,\ldots,3$ identify the legal rectangles with two copies of the sum-3 rectangles. A sum-3 rectangle has alternating complementary row profiles. Fixing the first profile makes the row choices independent. Each row is determined by its initial cell and the chosen edge sums, so the sum of the complementary fiber sizes is at most 5.

The resulting one- and two-step multipliers give the polynomial `(X-1)(X^2-2)(X^2-3)(X^2-4)(X^2-6)` in the forward shift. It annihilates each profile contribution and hence their sum. Expansion yields the published signed row, and transposition gives the other axis.

## Falsifier

An exact positive rectangle violating either equation would refute the common recurrence.

## Evidence

The Lean declaration proves the two literal identities with axiom closure `propext`, `Classical.choice` and `Quot.sound`.

## Triage

This theorem covers the single common recurrence on the two axes at the stated alphabet and stress.

## ASSUMED-UNVERIFIED

Global priority is unverified. The cited OEIS revisions establish the source clauses and signed coefficients.
