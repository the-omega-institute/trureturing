# Alternating Floor Square-Root Zero Blocks

## Abstract

Explicit disjoint zero blocks for alternating floor square-root differences.

**Definition 1.1 (The natural floor difference).**

$$\forall n \in \mathbb{N}, l \in \mathbb{N},\; \operatorname{d}\left(n, l\right) = \operatorname{isqrt}\left(2 \cdot l \cdot n\right) - \operatorname{isqrt}\left((2 \cdot l - 1) \cdot n\right)$$

*Formalization.* `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.d` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function is defined on natural n and l. Here isqrt is Nat.sqrt, the natural square root. Every subtraction in this formula is truncated natural subtraction, including 2*l-1 and the outer difference. Equation (2.3) of arXiv:2510.26291 assumes n odd, n at least one, and 1<=l<=div(n-1,2). Lean extends d to all natural n and l, and the next theorem proves the floor identity for every l at least one.

**Definition 1.2 (The explicit start function).**

$$\forall n \in \mathbb{N}, a \in \mathbb{N},\; \operatorname{blockStart}\left(n, a\right) = \operatorname{div}\left(n - 1, 2\right) + 1 + a - \operatorname{isqrt}\left(2 \cdot a \cdot n\right)$$

*Formalization.* `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.blockStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operator div denotes natural-number division, so div(n-1,2) is the half-range h. The displayed label a is Lean's lam. Both n-1 and the subtraction of isqrt are truncated natural subtractions. The formula is left-associated before the final subtraction. The zero-block theorem proves this start positive and its whole block within the half-range for every eligible label.

**Theorem 1.3 (Fidelity to real square-root floors).**

$$\forall n \in \mathbb{N}, l \in \mathbb{N},\; (1 \le l) \Rightarrow (\operatorname{int}\left(\operatorname{d}\left(n, l\right)\right) = \left\lfloor\sqrt{2 \cdot \operatorname{real}\left(l\right) \cdot \operatorname{real}\left(n\right)}\right\rfloor - \left\lfloor\sqrt{(2 \cdot \operatorname{real}\left(l\right) - 1) \cdot \operatorname{real}\left(n\right)}\right\rfloor)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.d_eq_floor_real_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The operators int and real are the canonical inclusions of natural numbers into the integers and reals. The square roots here are real, the floor values are integers, and both displayed subtractions on the right use their ordinary real or integer arithmetic. This bind-only encoding companion uses Real.floor_real_sqrt_eq_nat_sqrt and monotonicity. It is a separate interpretation theorem that can be combined with conjecture21; the Lean proof of conjecture21 itself depends on zero_block and blocks_disjoint.

**Theorem 1.4 (Complementary indices share one square-root interval).**

$$\forall n \in \mathbb{N}, h \in \mathbb{N}, a \in \mathbb{N}, k \in \mathbb{N},\; ((n = 2 \cdot h + 1) \land \left((1 \le a) \land \left((a \le h) \land \left((\operatorname{isqrt}\left((2 \cdot a - 1) \cdot n\right) + 2 \le k) \land (k \le \operatorname{isqrt}\left(2 \cdot a \cdot n\right))\right)\right)\right)) \Rightarrow (let l := h + 1 + a - k in (1 \le l) \land \left((l \le h) \land \left((k \le n) \land \left(((n - k)^{2} \le (2 \cdot l - 1) \cdot n) \land \left(((2 \cdot l - 1) \cdot n \le 2 \cdot l \cdot n) \land (2 \cdot l \cdot n < (n - k + 1)^{2})\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.witness_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All variables and arithmetic in this statement are natural; every subtraction is truncated. The label a is Lean's lam. The let-bound l is the complementary index h+1+lam-k. The two square inequalities have slacks 2*lam*n-k^2 and (k-1)^2-(2*lam-1)*n respectively, interpreted as integer differences: the first is nonnegative and the second strictly positive. This is the preregistered witness of candidate theorem 4.109. The dependency direction is conjecture21 to witness_bounds, through the zero and disjointness clauses.

**Theorem 1.5 (Every block offset has two equal complementary roots).**

$$\forall n \in \mathbb{N}, h \in \mathbb{N}, a \in \mathbb{N}, j \in \mathbb{N},\; ((n = 2 \cdot h + 1) \land \left(((1 \le a) \land \left((a \le h) \land (2 \le \operatorname{d}\left(n, a\right))\right)) \land (j \le (\operatorname{d}\left(n, a\right) - 2))\right)) \Rightarrow ((1 \le \operatorname{blockStart}\left(n, a\right) + j) \land \left((\operatorname{blockStart}\left(n, a\right) + j \le h) \land (\exists k \in \mathbb{N},\; (k \le n) \land \left((\operatorname{blockStart}\left(n, a\right) + j + k = h + 1 + a) \land \left((\operatorname{isqrt}\left((2 \cdot \left(\operatorname{blockStart}\left(n, a\right) + j\right) - 1) \cdot n\right) = n - k) \land (\operatorname{isqrt}\left(2 \cdot \left(\operatorname{blockStart}\left(n, a\right) + j\right) \cdot n\right) = n - k)\right)\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.block_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All variables and arithmetic are natural, and every subtraction is truncated. For each permitted offset j, the theorem exposes a complementary index k at most n, its label equation, and the two root equalities required by the atom. The dependency direction is zero_block and blocks_disjoint to block_point.

**Theorem 1.6 (Every entry of the consecutive block vanishes).**

$$\forall n \in \mathbb{N}, h \in \mathbb{N}, a \in \mathbb{N},\; ((n = 2 \cdot h + 1) \land ((1 \le a) \land \left((a \le h) \land (2 \le \operatorname{d}\left(n, a\right))\right))) \Rightarrow ((1 \le \operatorname{blockStart}\left(n, a\right)) \land \left((\operatorname{blockStart}\left(n, a\right) + (\operatorname{d}\left(n, a\right) - 2) \le h) \land (\forall j \in \mathbb{N},\; (j \le (\operatorname{d}\left(n, a\right) - 2)) \Rightarrow (\operatorname{d}\left(n, \operatorname{blockStart}\left(n, a\right) + j\right) = 0))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.zero_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every variable is natural; a is Lean's lam. Subtraction in d, blockStart, and d(n,lam)-2 is truncated natural subtraction; j begins at zero. The hypothesis d(n,lam) at least two makes the displayed inclusive block have d(n,lam)-1 entries. Both roots at each entry equal n-k by witness_bounds. This is the consecutive-zero and range clause of candidate theorem 4.109, with dependency direction conjecture21 to zero_block.

**Theorem 1.7 (A common index recovers its label).**

$$\forall n \in \mathbb{N}, h \in \mathbb{N}, a \in \mathbb{N}, b \in \mathbb{N}, l \in \mathbb{N}, k \in \mathbb{N}, j \in \mathbb{N},\; ((k \le n) \land \left((j \le n) \land \left((l + k = h + 1 + a) \land \left((l + j = h + 1 + b) \land (n - k = n - j)\right)\right)\right)) \Rightarrow ((k = j) \land (a = b))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.common_index_label_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All variables and arithmetic are natural, and subtraction is truncated. The bounds on k and j make equality of n-k and n-j recover k=j; the two common-index label equations then recover a=b. The dependency direction is blocks_disjoint to common_index_label_recovery.

**Theorem 1.8 (Distinct eligible labels have disjoint index blocks).**

$$\forall n \in \mathbb{N}, h \in \mathbb{N}, a \in \mathbb{N}, b \in \mathbb{N},\; ((n = 2 \cdot h + 1) \land \left(((1 \le a) \land \left((a \le h) \land (2 \le \operatorname{d}\left(n, a\right))\right)) \land \left(((1 \le b) \land \left((b \le h) \land (2 \le \operatorname{d}\left(n, b\right))\right)) \land (a \ne b)\right)\right)) \Rightarrow (\forall l \in \mathbb{N},\; ((\operatorname{blockStart}\left(n, a\right) \le l) \land \left((l \le \operatorname{blockStart}\left(n, a\right) + (\operatorname{d}\left(n, a\right) - 2)) \land \left((\operatorname{blockStart}\left(n, b\right) \le l) \land (l \le \operatorname{blockStart}\left(n, b\right) + (\operatorname{d}\left(n, b\right) - 2))\right)\right)) \Rightarrow (False))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.blocks_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All variables are natural; a and b are Lean's lam and mu. All subtractions in d, blockStart, and the endpoints are truncated natural subtraction. False means that no index l can satisfy all four membership bounds. A shared floor value forces equal complementary indices, then equal labels. This is the disjointness clause of candidate theorem 4.109, with dependency direction conjecture21 to blocks_disjoint.

**Theorem 1.9 (The full simultaneous zero-block theorem).**

$$\forall n \in \mathbb{N},\; ((1 \le n) \land (\operatorname{Odd}\left(n\right))) \Rightarrow (\exists s \in \mathbb{N} \to \mathbb{N},\; (\forall a \in \mathbb{N},\; ((1 \le a) \land \left((a \le \operatorname{div}\left(n - 1, 2\right)) \land (2 \le \operatorname{d}\left(n, a\right))\right)) \Rightarrow ((1 \le s\left(a\right)) \land \left((s\left(a\right) + (\operatorname{d}\left(n, a\right) - 2) \le \operatorname{div}\left(n - 1, 2\right)) \land (\forall j \in \mathbb{N},\; (j \le (\operatorname{d}\left(n, a\right) - 2)) \Rightarrow (\operatorname{d}\left(n, s\left(a\right) + j\right) = 0))\right))) \land (\forall a \in \mathbb{N}, b \in \mathbb{N},\; (((1 \le a) \land \left((a \le \operatorname{div}\left(n - 1, 2\right)) \land (2 \le \operatorname{d}\left(n, a\right))\right)) \land \left(((1 \le b) \land \left((b \le \operatorname{div}\left(n - 1, 2\right)) \land (2 \le \operatorname{d}\left(n, b\right))\right)) \land (a \ne b)\right)) \Rightarrow (\forall l \in \mathbb{N},\; ((s\left(a\right) \le l) \land \left((l \le s\left(a\right) + (\operatorname{d}\left(n, a\right) - 2)) \land \left((s\left(b\right) \le l) \land (l \le s\left(b\right) + (\operatorname{d}\left(n, b\right) - 2))\right)\right)) \Rightarrow (False))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.conjecture21` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This proves the whole statement registered as candidate theorem 4.109: one start function simultaneously supplies every eligible label's consecutive zero block and makes distinct blocks disjoint. The proof chooses s(lam)=blockStart(n,lam). All quantified values are natural; a and b are Lean's lam and mu. The operator div is natural-number division, and every subtraction in this display and in d is truncated natural subtraction. The positive-index floor identity above supplies the real-floor interpretation, including at all produced indices.

The conjecture's source is Chamberland and Dilcher, arXiv:2510.26291v1, section 2, equation (2.3) and Conjecture 2.1. That paper states that its proof is incomplete; it is the source of the problem, not an attestation of the proof given here. The range of labels is the definition's range from one through div(n-1,2). Disjointness refers to index intervals.

## References

- Truth anchor: `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.blockStart`
- Truth anchor: `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.block_point`
- Truth anchor: `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.blocks_disjoint`
- Truth anchor: `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.common_index_label_recovery`
- Truth anchor: `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.conjecture21`
- Truth anchor: `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.d`
- Truth anchor: `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.d_eq_floor_real_sqrt`
- Truth anchor: `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.witness_bounds`
- Truth anchor: `D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.zero_block`
