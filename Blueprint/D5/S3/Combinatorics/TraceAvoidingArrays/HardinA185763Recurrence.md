# Trace-avoiding binary arrays: A185763

## Abstract

Literal binary arrays, their neighboring block traces, and the exact recurrence for A185763.

**Definition 1.1 (Contiguous blocks).**

$$\forall n \in \operatorname{Nat},\; \forall a \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(4\right), \operatorname{Fin}\left(2\right)\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{block}\left(a, i, j\right) = \operatorname{fun} (u: \operatorname{Fin}\left(2\right)) \mapsto \operatorname{fun} (v: \operatorname{Fin}\left(2\right)) \mapsto (\operatorname{val}\left(a\left((\operatorname{if} u = 0 \operatorname{then} \operatorname{Fin}.\operatorname{castSucc}\left(i\right) \operatorname{else} \operatorname{Fin}.\operatorname{succ}\left(i\right)), (\operatorname{if} v = 0 \operatorname{then} \operatorname{Fin}.\operatorname{castSucc}\left(j\right) \operatorname{else} \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right) : \operatorname{Int})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.block` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

Number of (n+1) X 4 binary arrays with no 2 X 2 subblock trace equal to any horizontal or vertical neighbor 2 X 2 subblock trace. OEIS A185763, name field (unpaginated). A block selects adjacent rows and columns; its entries are embedded in the integers.

**Definition 1.2 (Unequal neighboring traces).**

$$\forall n \in \operatorname{Nat},\; \forall a \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(4\right), \operatorname{Fin}\left(2\right)\right),\; (\operatorname{valid}\left(a\right)) \Leftrightarrow ((\forall i \in \operatorname{Fin}\left(n\right),\; \forall k \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; (\operatorname{val}\left(k\right) = \operatorname{val}\left(i\right) + 1) \Rightarrow (\operatorname{Matrix}.\operatorname{trace}\left(\operatorname{block}\left(a, i, j\right)\right) \ne \operatorname{Matrix}.\operatorname{trace}\left(\operatorname{block}\left(a, k, j\right)\right))) \land (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \forall l \in \operatorname{Fin}\left(3\right),\; (\operatorname{val}\left(l\right) = \operatorname{val}\left(j\right) + 1) \Rightarrow (\operatorname{Matrix}.\operatorname{trace}\left(\operatorname{block}\left(a, i, j\right)\right) \ne \operatorname{Matrix}.\operatorname{trace}\left(\operatorname{block}\left(a, i, l\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.valid` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

Number of (n+1) X 4 binary arrays with no 2 X 2 subblock trace equal to any horizontal or vertical neighbor 2 X 2 subblock trace. OEIS A185763, name field (unpaginated). Matrix.trace is the sum of the two main-diagonal entries. Neighbors have origins differing by one in exactly one coordinate. Every array is labeled; no symmetry or boundary identification is imposed.

**Definition 1.3 (The literal array count).**

$$\forall n \in \operatorname{Nat},\; \operatorname{count}\left(n\right) = \operatorname{Nat}.\operatorname{card}\left(\{a: \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(4\right), \operatorname{Fin}\left(2\right)\right) \mid \operatorname{valid}\left(a\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.count` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

Number of (n+1) X 4 binary arrays with no 2 X 2 subblock trace equal to any horizontal or vertical neighbor 2 X 2 subblock trace. OEIS A185763, name field (unpaginated). The index n counts one fewer than the number of rows; the width is 4 and entries lie in Fin 2.

**Definition 1.4 (The zero-constant generating series).**

$$generatingSeries = \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (n: \operatorname{Nat}) \mapsto \operatorname{if} n = 0 \operatorname{then} 0 \operatorname{else} (\operatorname{count}\left(n\right) : \operatorname{Rat})\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.generatingSeries` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

The source has offset 1. The coefficient at zero is zero, and its coefficient at every positive index is the count of those arrays.

**Definition 1.5 (The published formulas).**

$$(claim) \Leftrightarrow ((\operatorname{count}\left(1\right) = 104) \land ((\operatorname{count}\left(2\right) = 368) \land ((\operatorname{count}\left(3\right) = 1408) \land ((\operatorname{count}\left(4\right) = 5272) \land ((\operatorname{count}\left(5\right) = 19992) \land ((\operatorname{count}\left(6\right) = 75192) \land ((\forall n \in \operatorname{Nat},\; (7 \le n) \Rightarrow ((\operatorname{count}\left(n\right) : \operatorname{Int}) = (\operatorname{count}\left(n - 1\right) : \operatorname{Int}) + 10 \cdot (\operatorname{count}\left(n - 2\right) : \operatorname{Int}) + 3 \cdot (\operatorname{count}\left(n - 3\right) : \operatorname{Int}) - 5 \cdot (\operatorname{count}\left(n - 4\right) : \operatorname{Int}) + (\operatorname{count}\left(n - 5\right) : \operatorname{Int}))) \land (\operatorname{let} X: \operatorname{PowerSeries}\left(\operatorname{Rat}\right):= \operatorname{PowerSeries}.\operatorname{X}; generatingSeries = 8 \cdot X \cdot (13 + 33 \cdot X - 16 \cdot (X)^{3} + 7 \cdot (X)^{4} - (X)^{5}) \cdot (1 - X - 10 \cdot (X)^{2} - 3 \cdot (X)^{3} + 5 \cdot (X)^{4} - (X)^{5})^{-1}))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.claim` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

Empirical: a(n) = a(n-1) + 10*a(n-2) + 3*a(n-3) - 5*a(n-4) + a(n-5) for n>6. Empirical g.f.: 8*x*(13 + 33*x - 16*x^3 + 7*x^4 - x^5) / (1 - x - 10*x^2 - 3*x^3 + 5*x^4 - x^5). - _Colin Barker_, Apr 16 2018 OEIS A185763, formula field (unpaginated). Counts in the recurrence are embedded in Int, and the formal series has coefficients in Rat.

**Theorem 1.6 (The formulas hold).**

$$(\operatorname{count}\left(1\right) = 104) \land ((\operatorname{count}\left(2\right) = 368) \land ((\operatorname{count}\left(3\right) = 1408) \land ((\operatorname{count}\left(4\right) = 5272) \land ((\operatorname{count}\left(5\right) = 19992) \land ((\operatorname{count}\left(6\right) = 75192) \land ((\forall n \in \operatorname{Nat},\; (7 \le n) \Rightarrow ((\operatorname{count}\left(n\right) : \operatorname{Int}) = (\operatorname{count}\left(n - 1\right) : \operatorname{Int}) + 10 \cdot (\operatorname{count}\left(n - 2\right) : \operatorname{Int}) + 3 \cdot (\operatorname{count}\left(n - 3\right) : \operatorname{Int}) - 5 \cdot (\operatorname{count}\left(n - 4\right) : \operatorname{Int}) + (\operatorname{count}\left(n - 5\right) : \operatorname{Int}))) \land (\operatorname{let} X: \operatorname{PowerSeries}\left(\operatorname{Rat}\right):= \operatorname{PowerSeries}.\operatorname{X}; generatingSeries = 8 \cdot X \cdot (13 + 33 \cdot X - 16 \cdot (X)^{3} + 7 \cdot (X)^{4} - (X)^{5}) \cdot (1 - X - 10 \cdot (X)^{2} - 3 \cdot (X)^{3} + 5 \cdot (X)^{4} - (X)^{5})^{-1})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2011). *Trace-avoiding binary arrays: OEIS A185761–A185764*. URL: <https://oeis.org/A185761>.

*Commentary.*

A bijection encodes each binary row by a finite integer. The adjacent-trace tests give pair and triple conditions on consecutive rows. Weighted classes of row pairs preserve all continuation counts. An exact matrix-vector identity propagates to every length and gives the recurrence; coefficient comparison gives the formal generating series. This result settles OEIS A185763 (external question #21315) as a member of the shared Hardin problem resolution recorded with A185761.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.block`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.claim`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.count`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.generatingSeries`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.valid`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
