---
slug: hardin-a235319-common-recurrence
bibkey: hardin2014a235319
doi: null
url: https://oeis.org/A235319
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence.a235319_all_rows_and_columns
---

# Hardin's common order-18 recurrence for A235319

## Problem

Let $T(n,k)$ count the literal indexed $(n+1)\times(k+1)$ arrays over $\{0,\ldots,6\}$ in which every contiguous $2\times2$ block has absolute diagonal difference 7. A235319 proposes a single recurrence for all rows and columns. A235317 gives the signed coefficients for column 6. [Table source](../Library/Automata/hardin2014a235319.md) · [Coefficient source](../Library/Automata/hardin2014a235317.md) · [Preregistration #34331](https://github.com/the-omega-institute/trureturing/issues/34331)

With $(c_1,\ldots,c_{18})=(4,47,-200,-901,4204,8957,-48440,-47194,334096,101948,-1410080,170136,3549696,-1446912,-4861440,2954880,2764800,-2073600)$, both equations hold for every $n,k\geq 1$.

$$
T(n+18,k)=\sum_{j=1}^{18}c_j T(n+18-j,k),
\qquad
T(n,k+18)=\sum_{j=1}^{18}c_j T(n,k+18-j).
$$

The two conjuncts of `a235319_all_rows_and_columns` use the integer cast of `C 6 7 n k`, the cardinality of the literal legal subtype. Its block predicate ranges over `Fin n` and `Fin k` and tests the natural absolute value of the integer difference of the two diagonal sums. The two positivity hypotheses include every fixed index starting at one. The first full window in either direction uses indices 1 through 19.

## Motivation

A235319 asks whether a single signed law holds along both axes, including at a fixed index of one. A235317 supplies the coefficients for one column.

## Gap

The coefficient row for column 6 determines the proposed law. Its validity at every positive pair of indices requires the two-axis theorem.

## Route

The checkerboard change of variables identifies the legal arrays with the sum-5 and sum-19 rectangles. Adjacent blocks share two cells, so their sums differ by at most 12. Each positive rectangle lies wholly in one class. Complementing every entry swaps the classes, and the sum-5 class uses entries from 0 through 5.

Successive rows have complementary horizontal edge-sum profiles. The initial cell determines a row with prescribed edge sums, giving a bound of 7 on the sum of the complementary fiber sizes. The two-step multiplier is their product. Equal sizes 1 and 3 give first-order factors. The resulting polynomial in the forward shift is

$$
(X-1)(X-3)(X^2-2)(X^2-3)(X^2-4)(X^2-5)(X^2-6)(X^2-8)(X^2-10)(X^2-12).
$$

It annihilates every profile contribution and hence their sum. Its exact expansion gives the signed coefficient row. Transposing the rectangles supplies the second identity.

## Falsifier

A positive pair of indices at which a literal count violates either identity would refute the common recurrence.

## Evidence

The Lean proof uses `propext`, `Classical.choice` and `Quot.sound`. The literal count and first full windows have exact Lean checks. [Independent acceptance](https://github.com/the-omega-institute/trureturing/issues/34331#issuecomment-7179475594)

## Triage

The theorem establishes the common axis recurrence at the given alphabet and stress.

## ASSUMED-UNVERIFIED

Global priority is unverified. Slice minimal order and diagonal recurrences are outside the stated scope.
