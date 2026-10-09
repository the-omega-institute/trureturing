# First occurrences in Kimberling's array

## Abstract

The first natural with v occurrences in the golden power array is the Lucas number of index four v minus five.

**Definition 1.1 (Occurrence count).**

$$\forall N \in \mathrm{Nat},\; \operatorname{a}\left(N\right) = \operatorname{card}\left(\left\{i \mid i \in \mathrm{Nat}, \left(1 \le i \land i \le N\right) \land N \in \operatorname{row}\left(i\right)\right\}\right)$$

*Formalization.* `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count the rows with indices between one and N that contain N. Membership implies that the row index is at most N.

**Definition 1.2 (First occurrence assertion).**

$$\mathrm{claim} \Leftrightarrow \left(\forall v \in \mathrm{Nat},\; 2 \le v \Rightarrow \left(\operatorname{a}\left(\operatorname{lucas}\left(4 \cdot v - 5\right)\right) = v \land \left(\forall N \in \mathrm{Nat},\; 1 \le N \Rightarrow \left(N < \operatorname{lucas}\left(4 \cdot v - 5\right) \Rightarrow \operatorname{a}\left(N\right) \ne v\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every v at least two, the target Lucas number has v occurrences and no smaller positive natural has exactly v occurrences.

**Theorem 1.3 (Initial Lucas value).**

$$\operatorname{lucas}\left(0\right) = 2$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zeroth Lucas number is two.

**Theorem 1.4 (Fibonacci bridge).**

$$\forall n \in \mathrm{Nat},\; \operatorname{lucas}\left(n + 1\right) = \operatorname{fib}\left(n\right) + \operatorname{fib}\left(n + 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral trace expresses each positive Lucas number as the sum of two Fibonacci numbers.

**Theorem 1.5 (Real Lucas identity).**

$$\forall n \in \mathrm{Nat},\; \operatorname{lucas}\left(n\right) = \mathrm{goldenRatio}^{n} + \mathrm{goldenConj}^{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two conjugate golden powers sum to the Lucas number.

**Theorem 1.6 (Positive Lucas numbers).**

$$\forall n \in \mathrm{Nat},\; 0 < \operatorname{lucas}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every Lucas number is positive.

**Theorem 1.7 (Lucas recurrence).**

$$\forall n \in \mathrm{Nat},\; \operatorname{lucas}\left(n + 2\right) = \operatorname{lucas}\left(n + 1\right) + \operatorname{lucas}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_recur` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lucas numbers satisfy the Fibonacci recurrence.

**Theorem 1.8 (Strict increase).**

$$\forall n \in \mathrm{Nat},\; 1 \le n \Rightarrow \operatorname{lucas}\left(n\right) < \operatorname{lucas}\left(n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lucas numbers strictly increase from index one onward.

**Theorem 1.9 (Lucas monotonicity).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; 1 \le n \Rightarrow \left(n \le m \Rightarrow \operatorname{lucas}\left(n\right) \le \operatorname{lucas}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Comparison of indices at least one gives comparison of Lucas numbers.

**Theorem 1.10 (Odd Lucas identity).**

$$\forall n \in \mathrm{Nat},\; \operatorname{Odd}\left(n\right) \Rightarrow \operatorname{lucas}\left(n\right) = \mathrm{goldenRatio}^{n} - \operatorname{inv}\left(\mathrm{goldenRatio}^{n}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_odd_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For odd indices the conjugate term is the negative inverse power.

**Theorem 1.11 (Even Lucas identity).**

$$\forall n \in \mathrm{Nat},\; \operatorname{Even}\left(n\right) \Rightarrow \operatorname{lucas}\left(n\right) = \mathrm{goldenRatio}^{n} + \operatorname{inv}\left(\mathrm{goldenRatio}^{n}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_even_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For even indices the conjugate term is the positive inverse power.

**Theorem 1.12 (Inverse-power bound).**

$$\operatorname{inv}\left(\mathrm{goldenRatio}\right) + \operatorname{inv}\left(\mathrm{goldenRatio}^{3}\right) < 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.inv_one_add_inv_cube_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse first and third golden powers sum to less than one.

**Theorem 1.13 (Own-row membership).**

$$\forall m \in \mathrm{Nat},\; \operatorname{Odd}\left(m\right) \Rightarrow \left(1 \le m \Rightarrow \operatorname{lucas}\left(m\right) \in \operatorname{row}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_mem_own_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an odd positive index, the first entry of the corresponding row is the Lucas number.

**Theorem 1.14 (Lower odd rows).**

$$\forall m \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \operatorname{Odd}\left(m\right) \Rightarrow \left(3 \le m \Rightarrow \left(\operatorname{Odd}\left(i\right) \Rightarrow \left(1 \le i \Rightarrow \left(2 \cdot i < m \Rightarrow \operatorname{lucas}\left(m\right) \in \operatorname{row}\left(i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_mem_lower_odd_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An odd Lucas number belongs to every positive odd row whose doubled index is smaller than the Lucas index. The multiplier is the Lucas number at the difference of the indices.

**Theorem 1.15 (Pair lower bound).**

$$\forall i \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \forall N \in \mathrm{Nat},\; 1 \le i \Rightarrow \left(i < j \Rightarrow \left(N \in \operatorname{row}\left(i\right) \Rightarrow \left(N \in \operatorname{row}\left(j\right) \Rightarrow \operatorname{lucas}\left(2 \cdot i + 1\right) \le N\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.pair_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common value in two rows is at least the odd Lucas threshold of the lower row. Below that threshold the golden difference has absolute norm one. Even gaps contradict the power threshold; odd gaps place the two multiples on opposite sides of an integer.

**Theorem 1.16 (Threshold for at least v rows).**

$$\forall N \in \mathrm{Nat},\; \forall v \in \mathrm{Nat},\; 2 \le v \Rightarrow \left(v \le \operatorname{a}\left(N\right) \Rightarrow \operatorname{lucas}\left(4 \cdot v - 5\right) \le N\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.occurrence_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordered containing rows have gaps at least two. The penultimate one among v rows has index at least twice v minus three, so the pair bound gives the asserted Lucas threshold.

**Theorem 1.17 (Threshold attainment).**

$$\forall v \in \mathrm{Nat},\; 2 \le v \Rightarrow \operatorname{a}\left(\operatorname{lucas}\left(4 \cdot v - 5\right)\right) = v$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rows one, three, through twice v minus three, together with row four v minus five, provide v occurrences. Any additional occurrence would violate the next Lucas threshold.

**Theorem 1.18 (First occurrences).**

$$\mathrm{claim}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/kimberling-array-first-occurrence-l4v5` (proved) by `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kimberling-array-first-occurrence-l4v5","declaration_gid":"D5/S1/Recurrence/KimberlingArrayFirstOccurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Threshold attainment and the lower bound prove the first-occurrence assertion for every v at least two.

## References

- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.a`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.claim`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.inv_one_add_inv_cube_lt_one`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_attainment`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_even_real`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_mem_lower_odd_row`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_mem_own_row`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_mono`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_odd_real`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_pos`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_real`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_recur`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_strict`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_succ`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_zero`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.occurrence_lower_bound`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.pair_lower_bound`
- Truth anchor: `D5/S1/Recurrence/KimberlingArrayFirstOccurrence.result`
- Dependency: [D5/S1/Recurrence/GoldenPartition](GoldenPartition.md)
- Dependency: [D5/S1/Recurrence/KimberlingArrayRowPairs](KimberlingArrayRowPairs.md)
