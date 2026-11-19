# Increasing two-bit windows: A202330

## Abstract

All labeled four-column Boolean arrays whose consecutive two-bit windows are nondecreasing in every row and column.

**Definition 1.1 (Integer bit values).**

$$\forall b \in \operatorname{Bool},\; \operatorname{bit}\left(b\right) = \operatorname{if} b = \operatorname{true} \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.bit` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2018). *OEIS A202330: four-column binary arrays with nondecreasing two-bit windows*. URL: <https://oeis.org/A202330>.

*Commentary.*

A Boolean bit is mapped into the integers before addition or multiplication.

**Definition 1.2 (Horizontal windows).**

$$\forall r \in \operatorname{Fin}\left(4\right)\to\operatorname{Bool},\; (\operatorname{horizontal}\left(r\right)) \Leftrightarrow (\forall j \in \operatorname{Fin}\left(2\right),\; 2 \cdot \operatorname{bit}\left(r\left(j\right)\right) + \operatorname{bit}\left(r\left(j + 1\right)\right) \le 2 \cdot \operatorname{bit}\left(r\left(j + 1\right)\right) + \operatorname{bit}\left(r\left(j + 2\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.horizontal` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2018). *OEIS A202330: four-column binary arrays with nondecreasing two-bit windows*. URL: <https://oeis.org/A202330>.

*Commentary.*

The two comparisons use positions 0,1,2 and 1,2,3. Their window values are ordinary binary integers.

**Definition 1.3 (The native array predicate).**

$$\forall n \in \operatorname{Nat},\; \forall a \in (\operatorname{Fin}\left(n + 1\right)\times\operatorname{Fin}\left(4\right))\to\operatorname{Bool},\; (\operatorname{valid}\left(a\right)) \Leftrightarrow ((\forall i \in \operatorname{Fin}\left(n + 1\right),\; \operatorname{horizontal}\left(\operatorname{fun} (j: \operatorname{Fin}\left(4\right)) \mapsto a\left(i, j\right)\right)) \land (\forall i \in \operatorname{Nat},\; (i + 2 < n + 1) \Rightarrow (\forall j \in \operatorname{Fin}\left(4\right),\; 2 \cdot \operatorname{bit}\left(a\left(i, j\right)\right) + \operatorname{bit}\left(a\left(i + 1, j\right)\right) \le 2 \cdot \operatorname{bit}\left(a\left(i + 1, j\right)\right) + \operatorname{bit}\left(a\left(i + 2, j\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.valid` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2018). *OEIS A202330: four-column binary arrays with nondecreasing two-bit windows*. URL: <https://oeis.org/A202330>.

*Commentary.*

Every row satisfies both horizontal comparisons. In each column every three consecutive rows satisfy the same inequality. Coordinates and row order are retained; all boundaries are open.

**Definition 1.4 (Native cardinality).**

$$\forall n \in \operatorname{Nat},\; \operatorname{count}\left(n\right) = \operatorname{Nat}.\operatorname{card}\left(\{a: (\operatorname{Fin}\left(n + 1\right)\times\operatorname{Fin}\left(4\right))\to\operatorname{Bool} \mid \operatorname{valid}\left(a\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.count` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2018). *OEIS A202330: four-column binary arrays with nondecreasing two-bit windows*. URL: <https://oeis.org/A202330>.

*Commentary.*

The count is the cardinality of all labeled functions on the source coordinates satisfying valid. No sorting, symmetry quotient or value computed from the formula defines the count.

**Definition 1.5 (Zero-constant formal series).**

$$generatingSeries = \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (n: \operatorname{Nat}) \mapsto \operatorname{if} n = 0 \operatorname{then} 0 \operatorname{else} (\operatorname{count}\left(n\right) : \operatorname{Rat})\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.generatingSeries` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2018). *OEIS A202330: four-column binary arrays with nondecreasing two-bit windows*. URL: <https://oeis.org/A202330>.

*Commentary.*

The source offset is 1,1. Positive coefficients are native counts. The coefficient at zero is zero, independently of the native height-one array count.

**Definition 1.6 (The three source formulas).**

$$(claim) \Leftrightarrow ((\forall n \in \operatorname{Nat},\; (1 \le n) \Rightarrow (12 \cdot (\operatorname{count}\left(n\right) : \operatorname{Int}) = ((n : \operatorname{Int}))^{4} + 16 \cdot ((n : \operatorname{Int}))^{3} + 83 \cdot ((n : \operatorname{Int}))^{2} + 176 \cdot (n : \operatorname{Int}) + 156)) \land ((\operatorname{let} X: \operatorname{PowerSeries}\left(\operatorname{Rat}\right):= \operatorname{PowerSeries}.\operatorname{X}; generatingSeries = X \cdot (36 - 98 \cdot X + 112 \cdot (X)^{2} - 61 \cdot (X)^{3} + 13 \cdot (X)^{4}) \cdot ((1 - X)^{5})^{-1}) \land (\forall n \in \operatorname{Nat},\; (6 \le n) \Rightarrow ((\operatorname{count}\left(n\right) : \operatorname{Int}) = 5 \cdot (\operatorname{count}\left(n - 1\right) : \operatorname{Int}) - 10 \cdot (\operatorname{count}\left(n - 2\right) : \operatorname{Int}) + 10 \cdot (\operatorname{count}\left(n - 3\right) : \operatorname{Int}) - 5 \cdot (\operatorname{count}\left(n - 4\right) : \operatorname{Int}) + (\operatorname{count}\left(n - 5\right) : \operatorname{Int})))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.claim` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2018). *OEIS A202330: four-column binary arrays with nondecreasing two-bit windows*. URL: <https://oeis.org/A202330>.

*Commentary.*

The empirical quartic and Barker's conjectural generating function and recurrence refer to the same native count. Subtractions in the recurrence take place in the integers, and the formal series has rational coefficients.

**Theorem 1.7 (The full counting identity).**

$$(\forall n \in \operatorname{Nat},\; (1 \le n) \Rightarrow (12 \cdot (\operatorname{count}\left(n\right) : \operatorname{Int}) = ((n : \operatorname{Int}))^{4} + 16 \cdot ((n : \operatorname{Int}))^{3} + 83 \cdot ((n : \operatorname{Int}))^{2} + 176 \cdot (n : \operatorname{Int}) + 156)) \land ((\operatorname{let} X: \operatorname{PowerSeries}\left(\operatorname{Rat}\right):= \operatorname{PowerSeries}.\operatorname{X}; generatingSeries = X \cdot (36 - 98 \cdot X + 112 \cdot (X)^{2} - 61 \cdot (X)^{3} + 13 \cdot (X)^{4}) \cdot ((1 - X)^{5})^{-1}) \land (\forall n \in \operatorname{Nat},\; (6 \le n) \Rightarrow ((\operatorname{count}\left(n\right) : \operatorname{Int}) = 5 \cdot (\operatorname{count}\left(n - 1\right) : \operatorname{Int}) - 10 \cdot (\operatorname{count}\left(n - 2\right) : \operatorname{Int}) + 10 \cdot (\operatorname{count}\left(n - 3\right) : \operatorname{Int}) - 5 \cdot (\operatorname{count}\left(n - 4\right) : \operatorname{Int}) + (\operatorname{count}\left(n - 5\right) : \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-barker-a202330` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-barker-a202330","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2018). *OEIS A202330: four-column binary arrays with nondecreasing two-bit windows*. URL: <https://oeis.org/A202330>.

*Commentary.*

The six horizontal rows are 0000,0001,0010,0011,0111,1111. An exact row equivalence retains all 36 ordered pairs, including the incomparable rows 0001 and 0010. The transfer counts have the vector invariant 12 times T to the power m applied to the all-ones vector equals V(m), for every m at least two. Its initial identity and polynomial transition identity prove the quartic by induction; the actual two smaller counts are 36 and 82. The fifth difference gives the signed recurrence. Coefficient comparison, including the zero coefficient, gives the formal generating function.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.bit`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.claim`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.count`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.generatingSeries`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.horizontal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.valid`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
