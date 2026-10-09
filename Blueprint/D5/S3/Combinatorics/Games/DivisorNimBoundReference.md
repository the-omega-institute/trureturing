# Bounds from a Distinguished Heap

## Abstract

A distinguished heap bounds removal amounts and divisor counts. Separating moves that preserve this heap from moves that replace it gives a uniform recurrence for the Sprague–Grundy value.

**Theorem 1.1 (The reference heap bounds every removal).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall h \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall H \in \mathrm{Nat},\; \left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{mem}\left(m, P\right) \land \left(m \le H \land \operatorname{legal}\left(P, h, d\right)\right)\right)\right) \Rightarrow d \le H$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.removal_le_reference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A removal from the reference heap is at most its size. A removal elsewhere divides that positive size and is therefore no larger.

**Theorem 1.2 (An unchanged reference heap survives).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall h \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \left(\operatorname{mem}\left(m, P\right) \land m \ne h\right) \Rightarrow \operatorname{mem}\left(m, \operatorname{successor}\left(P, h, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.reference_survives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Changing a different heap retains the reference occurrence.

**Theorem 1.3 (A positive remainder is retained).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall h \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; d < h \Rightarrow \operatorname{mem}\left(h - d, \operatorname{successor}\left(P, h, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.changed_reference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A removal smaller than the changed heap leaves its positive remainder in the board.

**Theorem 1.4 (Lower removals retain a reference ceiling).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall h \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall H \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k\right) \land \left(\operatorname{mem}\left(h, P\right) \land \left(\operatorname{mem}\left(m, P\right) \land \left(m \le H \land \left(\operatorname{legal}\left(P, h, d\right) \land \operatorname{valuation}\left(d\right) < k\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists n \in \mathrm{Nat},\; \operatorname{mem}\left(n, \operatorname{successor}\left(P, h, d\right)\right) \land n \le H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.lower_reference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A lower-depth removal cannot empty the changed heap. Either the original reference survives or its positive remainder is no larger.

**Theorem 1.5 (Counting high-depth removals).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall k \in \mathrm{Nat},\; \forall e \in \mathrm{Nat},\; \forall B \in \mathrm{Nat},\; \forall A \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k\right) \land \left(\operatorname{mem}\left(e, P\right) \land \left(\operatorname{valuation}\left(e\right) = k \land \left(\left(\forall h \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \left(\operatorname{mem}\left(h, P\right) \land \left(\operatorname{legal}\left(P, h, d\right) \land \operatorname{valuation}\left(d\right) < k\right)\right) \Rightarrow \operatorname{grundy}\left(\operatorname{successor}\left(P, h, d\right)\right) \le B\right) \land \left(\forall d \in \mathrm{Nat},\; \left(\operatorname{legal}\left(P, e, d\right) \land k \le \operatorname{valuation}\left(d\right)\right) \Rightarrow \operatorname{mem}\left(d, A\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{grundy}\left(P\right) \le B + \operatorname{card}\left(A\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.dyadic_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero parent, a nonzero high-depth follower changes its unique minimum-depth heap. A finite set of eligible removal amounts bounds the number of exceptional followers.

**Theorem 1.6 (The coarse ceiling at depth zero).**

$$\forall H \in \mathrm{Nat},\; \operatorname{coarseBound}\left(0, H\right) = H + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarseBound_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The depth-zero ceiling is H plus one.

**Theorem 1.7 (Successive coarse ceilings).**

$$\forall k \in \mathrm{Nat},\; \forall H \in \mathrm{Nat},\; \operatorname{coarseBound}\left(k + 1, H\right) = \operatorname{coarseBound}\left(k, H\right) + \operatorname{div}\left(H, 2^{k + 1}\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarseBound_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The next ceiling adds the number of positive multiples of the next depth power that fit below H, followed by one mex increment.

**Theorem 1.8 (The coarse ceiling increases with depth).**

$$\forall H \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; j \le k \Rightarrow \operatorname{coarseBound}\left(j, H\right) \le \operatorname{coarseBound}\left(k, H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarseBound_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every increment is nonnegative.

**Theorem 1.9 (The divisible geometric sum).**

$$\forall k \in \mathrm{Nat},\; \forall H \in \mathrm{Nat},\; \operatorname{dvd}\left(2^{k}, H\right) \Rightarrow \operatorname{coarseBound}\left(k, H\right) + \operatorname{div}\left(H, 2^{k}\right) = 2 \cdot H + k + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarseBound_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the depth power divides H, the geometric sum and its last quotient add to twice H, with the depth-dependent mex increments.

**Theorem 1.10 (Large odd factors suffice).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \left(0 < u \land \left(k \le v \land v + 1 \le u\right)\right) \Rightarrow \operatorname{coarseBound}\left(k, 2^{v} \cdot u\right) \le 2 \cdot 2^{v} \cdot u$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarseBound_le_reference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the odd factor is at least v plus one, the terminal quotient absorbs all depth-dependent increments and the ceiling is at most twice the heap.

**Theorem 1.11 (The ceiling after changing the reference).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \left(0 < u \land j < v\right) \Rightarrow \operatorname{coarseBound}\left(j, 2^{v} \cdot u - 2^{j}\right) = \operatorname{changedBound}\left(v, u, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.changed_coarseBound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the smallest amount of valuation j from the reference gives the explicit changed-reference ceiling.

**Theorem 1.12 (A uniform coarse Grundy bound).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall k \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall H \in \mathrm{Nat},\; \left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k\right) \land \left(\operatorname{mem}\left(m, P\right) \land m \le H\right)\right)\right) \Rightarrow \operatorname{grundy}\left(P\right) \le \operatorname{coarseBound}\left(k, H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarse_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on depth bounds lower-depth followers. Higher-depth nonzero followers can arise only on a unique minimum heap, and their removal amounts are multiples of the depth power bounded by H.

**Definition 1.13 (Divisors above a dyadic threshold).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{highDivisors}\left(m, k\right) = \{d \in \operatorname{divisors}\left(m\right) | \operatorname{dvd}\left(2^{k}, d\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimBoundReference.highDivisors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep divisors of m that are multiples of the depth power.

**Theorem 1.14 (Division injects eligible removals into quotient divisors).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \left(0 < m \land \operatorname{dvd}\left(2^{k}, m\right)\right) \Rightarrow \operatorname{card}\left(\operatorname{highDivisors}\left(m, k\right)\right) \le \operatorname{card}\left(\operatorname{divisors}\left(\operatorname{div}\left(m, 2^{k}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.highDivisors_card_le_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dividing an eligible removal by the depth power gives a divisor of the reference quotient. Multiplication by that power recovers the removal.

**Theorem 1.15 (A divisor-count product bound).**

$$\forall w \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \operatorname{card}\left(\operatorname{divisors}\left(2^{w} \cdot u\right)\right) \le \left(w + 1\right) \cdot \operatorname{oddDivisorCount}\left(u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.divisor_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every divisor of a product is a product of divisors. The power of two has w plus one divisors, which bounds the cardinality by the product.

**Theorem 1.16 (The high-removal divisor ceiling).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \left(0 < u \land k \le v\right) \Rightarrow \operatorname{card}\left(\operatorname{highDivisors}\left(2^{v} \cdot u, k\right)\right) \le \left(v - k + 1\right) \cdot \operatorname{oddDivisorCount}\left(u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.highDivisors_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient has the remaining power of two and the original odd factor, giving at most v minus k plus one times the odd-factor divisor count.

**Theorem 1.17 (The depth of the distinguished heap).**

$$\forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \left(0 < u \land \operatorname{mod}\left(u, 2\right) = 1\right) \Rightarrow \operatorname{valuation}\left(2^{v} \cdot u\right) = v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.reference_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by a positive odd factor leaves the valuation of the power of two unchanged.

**Theorem 1.18 (Lower-depth followers preserve or change the reference).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall B \in \mathrm{Nat},\; \left(\left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k\right) \land \left(\operatorname{mem}\left(2^{v} \cdot u, P\right) \land \left(0 < u \land \left(\operatorname{mod}\left(u, 2\right) = 1 \land k \le v\right)\right)\right)\right)\right) \land \left(\left(\forall Q \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall j \in \mathrm{Nat},\; \left(\operatorname{Positive}\left(Q\right) \land \left(j < k \land \left(\operatorname{HasDepth}\left(Q, j\right) \land \operatorname{mem}\left(2^{v} \cdot u, Q\right)\right)\right)\right) \Rightarrow \operatorname{grundy}\left(Q\right) \le B\right) \land \left(\forall j \in \mathrm{Nat},\; j < k \Rightarrow \operatorname{changedBound}\left(v, u, j\right) \le B\right)\right)\right) \Rightarrow \left(\forall h \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \left(\operatorname{mem}\left(h, P\right) \land \left(\operatorname{legal}\left(P, h, d\right) \land \operatorname{valuation}\left(d\right) < k\right)\right) \Rightarrow \operatorname{grundy}\left(\operatorname{successor}\left(P, h, d\right)\right) \le B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.reference_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An unchanged reference invokes the earlier distinguished-heap bound. A changed reference invokes the coarse ceiling for its smaller remainder.

**Theorem 1.19 (The distinguished-heap recurrence step).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall B \in \mathrm{Nat},\; \left(\left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k\right) \land \left(\operatorname{mem}\left(2^{v} \cdot u, P\right) \land \left(0 < u \land \left(\operatorname{mod}\left(u, 2\right) = 1 \land k \le v\right)\right)\right)\right)\right) \land \left(\left(\forall Q \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall j \in \mathrm{Nat},\; \left(\operatorname{Positive}\left(Q\right) \land \left(j < k \land \left(\operatorname{HasDepth}\left(Q, j\right) \land \operatorname{mem}\left(2^{v} \cdot u, Q\right)\right)\right)\right) \Rightarrow \operatorname{grundy}\left(Q\right) \le B\right) \land \left(\forall j \in \mathrm{Nat},\; j < k \Rightarrow \operatorname{changedBound}\left(v, u, j\right) \le B\right)\right)\right) \Rightarrow \operatorname{grundy}\left(P\right) \le B + \operatorname{exceptionalCount}\left(v, u, k\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.reference_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Below the reference valuation, high removals divide the unchanged reference. At its valuation, high removals on the unique minimum are multiples of its depth power fitting within its size.

**Theorem 1.20 (The recurrence bounds every containing board).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall v \in \mathrm{Nat},\; \forall u \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \left(\left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k\right) \land \left(\operatorname{mem}\left(2^{v} \cdot u, P\right) \land \left(0 < u \land \left(\operatorname{mod}\left(u, 2\right) = 1 \land k \le v\right)\right)\right)\right)\right) \land 0 < v\right) \Rightarrow \operatorname{grundy}\left(P\right) \le \operatorname{recurrenceBound}\left(v, u, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundReference.reference_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction on depth combines all earlier containing-board bounds with the changed-reference ceilings. The number of other heaps is unrestricted.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.changed_coarseBound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.changed_reference`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarseBound_balance`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarseBound_le_reference`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarseBound_mono`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarseBound_succ`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarseBound_zero`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.coarse_bound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.divisor_card_le`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.dyadic_step`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.highDivisors`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.highDivisors_card_le`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.highDivisors_card_le_quotient`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.lower_reference`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.reference_bound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.reference_lower`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.reference_step`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.reference_survives`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.reference_valuation`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundReference.removal_le_reference`
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic](DivisorNimBoundArithmetic.md)
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimBoundOutcome](DivisorNimBoundOutcome.md)
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimGrundy](DivisorNimGrundy.md)
