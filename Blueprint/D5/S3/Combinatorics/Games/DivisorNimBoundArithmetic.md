# Distinguished-Heap Recurrence Estimates

## Abstract

A divisor-sensitive integer recurrence bounds the values associated with a distinguished heap.

**Definition 1.1 (Coarse ceiling).**

$$\forall k \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; \operatorname{coarseBound}\left(k, h\right) = \sum_{j \in \operatorname{range}\left(k + 1\right)} \operatorname{div}\left(h, 2^{j}\right) + k + 1$$

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.coarseBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coarse ceiling adds the quotients by successive powers of two and one unit for each depth.

**Definition 1.2 (Divisor count).**

$$\forall u \in \mathrm{Nat},\; \operatorname{oddDivisorCount}\left(u\right) = \operatorname{card}\left(\operatorname{divisors}\left(u\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.oddDivisorCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The divisor count is the cardinality of the positive-divisor set.

**Definition 1.3 (Changed reference heap).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \operatorname{changedBound}\left(v, u, j\right) = 2 \cdot 2^{v} \cdot u - \operatorname{div}\left(2^{v} \cdot u, 2^{j}\right) - 2^{j + 1} + j + 2$$

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.changedBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The changed-reference ceiling accounts for the subtraction of a removal of lower valuation.

**Definition 1.4 (Exceptional removals).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{exceptionalCount}\left(v, u, k\right) = \operatorname{if}\left(k = v, u, \left(v - k + 1\right) \cdot \operatorname{oddDivisorCount}\left(u\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.exceptionalCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Below the distinguished valuation the divisor count controls exceptional removals; at that valuation the odd part controls them.

**Definition 1.5 (Distinguished-heap recurrence).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \operatorname{recurrenceBound}\left(v, u, 0\right) = \left(v + 1\right) \cdot \operatorname{oddDivisorCount}\left(u\right) + 1 \land \left(\forall k \in \mathrm{Nat},\; \operatorname{recurrenceBound}\left(v, u, k + 1\right) = \operatorname{max}\left(\operatorname{recurrenceBound}\left(v, u, k\right), \max_{j \in \operatorname{range}\left(k + 1\right)} \operatorname{changedBound}\left(v, u, j\right)\right) + \operatorname{exceptionalCount}\left(v, u, k + 1\right) + 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.recurrenceBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each depth take the largest previous ceiling and add the exceptional-removal count and one. A supremum over an empty set of natural numbers is zero.

**Definition 1.6 (Terminal recurrence ceiling).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \operatorname{bound}\left(v, u\right) = \operatorname{recurrenceBound}\left(v, u, v\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.bound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The terminal ceiling is the recurrence evaluated at the distinguished valuation.

**Theorem 1.7 (Increasing depth ceiling).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; i \le j \Rightarrow \operatorname{recurrenceBound}\left(v, u, i\right) \le \operatorname{recurrenceBound}\left(v, u, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.recurrenceBound_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each recurrence step contains its predecessor in the maximum and adds nonnegative quantities.

**Theorem 1.8 (Divisor count ceiling).**

$$\forall u \in \mathrm{Nat},\; \operatorname{oddDivisorCount}\left(u\right) \le u$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.oddDivisorCount_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive divisor of u lies in the interval from one through u.

**Theorem 1.9 (Finite valuation range).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \left(1 \le v \land \left(v \le 15 \land \left(1 \le u \land \left(u \le v \land \left(\operatorname{mod}\left(u, 2\right) = 1 \land \left(\neg \left(u = 1 \land v \le 3\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{bound}\left(v, u\right) \le 2 \cdot 2^{v} \cdot u$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.finite_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For valuations one through fifteen and positive odd parts at most the valuation, the ceiling is at most twice the heap, apart from the three odd-part-one exceptions.

**Definition 1.10 (Triangular budget).**

$$\forall v \in \mathrm{Nat},\; \operatorname{triangle}\left(v\right) = \operatorname{div}\left(v \cdot \left(v + 1\right), 2\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.triangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The triangular budget sums the coefficients of the exceptional-removal counts.

**Theorem 1.11 (Doubled triangular budget).**

$$\forall v \in \mathrm{Nat},\; 2 \cdot \operatorname{triangle}\left(v\right) = v \cdot \left(v + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.triangle_twice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of two consecutive natural numbers is even.

**Theorem 1.12 (Exponential square estimate).**

$$\forall v \in \mathrm{Nat},\; 16 \le v \Rightarrow v \cdot \left(\operatorname{triangle}\left(v\right) + 2 \cdot v + 1\right)^{2} \le 2^{v + 3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_exponential_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After translating the valuation by sixteen, the consecutive-value comparison becomes a polynomial with nonnegative coefficients. Induction compares it with the doubling exponential.

**Theorem 1.13 (Exponential linear estimate).**

$$\forall v \in \mathrm{Nat},\; 16 \le v \Rightarrow \operatorname{triangle}\left(v\right) + 2 \cdot v + 2 \le 2^{v + 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_exponential_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same consecutive-value comparison bounds the quadratic budget by the doubling exponential.

**Theorem 1.14 (Unrolled recurrence ceiling).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \left(k \le v \land \left(\operatorname{recurrenceBound}\left(v, u, 0\right) \le n \land \left(\forall j \in \mathrm{Nat},\; j < v \Rightarrow \operatorname{changedBound}\left(v, u, j\right) \le n\right)\right)\right) \Rightarrow \operatorname{recurrenceBound}\left(v, u, k\right) \le n + \sum_{i \in \operatorname{range}\left(k\right)} \operatorname{exceptionalCount}\left(v, u, i + 1\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.recurrence_le_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common ceiling for the initial value and every changed-reference ceiling leaves only the sum of recurrence increments.

**Theorem 1.15 (Descending coefficient sum).**

$$\forall v \in \mathrm{Nat},\; \sum_{i \in \operatorname{range}\left(v\right)} v - i = \operatorname{triangle}\left(v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.sum_descending` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflecting the summation interval identifies the descending sum with the triangular budget.

**Theorem 1.16 (Total recurrence increments).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \sum_{i \in \operatorname{range}\left(v\right)} \operatorname{exceptionalCount}\left(v, u, i + 1\right) + 1 \le \operatorname{triangle}\left(v\right) \cdot u + v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.total_increment_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bound the divisor count by the odd part and sum the resulting descending coefficients.

**Theorem 1.17 (Lower-valuation gap).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \left(\left(16 \le v \land \left(1 \le u \land u \le v\right)\right) \land j < v\right) \Rightarrow \operatorname{triangle}\left(v\right) \cdot u + 2 \cdot v + 1 \le \operatorname{div}\left(2^{v} \cdot u, 2^{j}\right) + 2^{j + 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient and power-of-two terms have product twice the heap. The arithmetic mean-geometric mean inequality and the exponential square estimate supply the gap.

**Theorem 1.18 (Changed ceiling with budget).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \left(\left(16 \le v \land \left(1 \le u \land u \le v\right)\right) \land j < v\right) \Rightarrow \operatorname{changedBound}\left(v, u, j\right) + \operatorname{triangle}\left(v\right) \cdot u + v \le 2 \cdot 2^{v} \cdot u$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_changedBound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The gap pays for the whole recurrence budget and the lower-valuation additive terms.

**Theorem 1.19 (Initial ceiling with budget).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \left(16 \le v \land 1 \le u\right) \Rightarrow \operatorname{recurrenceBound}\left(v, u, 0\right) + \operatorname{triangle}\left(v\right) \cdot u + v \le 2 \cdot 2^{v} \cdot u$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential linear estimate pays for the initial divisor count and the entire recurrence budget.

**Theorem 1.20 (All large valuations).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \left(16 \le v \land \left(1 \le u \land u \le v\right)\right) \Rightarrow \operatorname{bound}\left(v, u\right) \le 2 \cdot 2^{v} \cdot u$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unroll the recurrence using the initial and changed-reference ceilings, then spend the triangular budget. Every valuation at least sixteen satisfies the twice-heap bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.bound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.changedBound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.coarseBound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.exceptionalCount`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.finite_bound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_bound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_changedBound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_exponential_linear`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_exponential_square`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_gap`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.large_initial`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.oddDivisorCount`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.oddDivisorCount_le`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.recurrenceBound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.recurrenceBound_mono`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.recurrence_le_budget`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.sum_descending`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.total_increment_le`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.triangle`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.triangle_twice`
