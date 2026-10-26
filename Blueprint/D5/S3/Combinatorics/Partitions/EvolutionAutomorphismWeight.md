# Sharp multiplicity weights of integer partitions

## Abstract

The multiplicity weight of a positive integer partition has six exceptional maxima and equals the factorial maximum from dimension seven onward. The maxima absorb a factorial of the remaining dimension with a shift by one.

**Definition 1.1 (Multiplicity weight).**

$$\forall p \in \operatorname{Multiset}\left(Nat\right),\; \operatorname{weight}\left(p\right) = \prod_{l \in \operatorname{toFinset}\left(p\right)}((l\cdot(2^{l}-1))^{\operatorname{count}\left(p, l\right)}\cdot\operatorname{count}\left(p, l\right)!)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a multiset of natural parts, multiply once for each distinct part l. If l occurs m times, its factor is (l times (2 to the l minus one)) to the m times m factorial. Parts equal to one are retained: their factor is the factorial of their multiplicity.

**Definition 1.2 (Maximum over positive partitions).**

$$\forall n \in Nat,\; \operatorname{maximumWeight}\left(n\right) = \max_{p\in\operatorname{Partition}\left(n\right)}\operatorname{weight}\left(\operatorname{parts}\left(p\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.maximumWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum is the finite supremum over Mathlib's Nat.Partition n. Its parts are positive and sum to n. The existing finite supremum attainment theorem gives an attaining partition, including at the neutral dimension zero.

**Theorem 1.3 (The factorial bound).**

$$\forall n \in Nat,\; 7 \le n \Rightarrow (\forall p \in \operatorname{Partition}\left(n\right),\; \operatorname{weight}\left(\operatorname{parts}\left(p\right)\right) \le n!)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.weight_le_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive part l at least six, l times (2 to the l minus one) is at most l factorial. Mathlib's uniformBell_mul_eq lifts this estimate to each multiplicity group. For lengths two, three, four and five, the factorial estimate starts at multiplicities four, three, two and two respectively; choose_mul_add propagates it. A numerical majorant with the six exceptional values is supermultiplicative. Combining distinct groups therefore bounds the complete partition weight by that majorant at the sum of the parts.

**Theorem 1.4 (The six exceptional maxima).**

$$\operatorname{maximumWeight}\left(1\right) = 1 \land (\operatorname{maximumWeight}\left(2\right) = 6 \land (\operatorname{maximumWeight}\left(3\right) = 21 \land (\operatorname{maximumWeight}\left(4\right) = 72 \land (\operatorname{maximumWeight}\left(5\right) = 155 \land (\operatorname{maximumWeight}\left(6\right) = 1296)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.maximum_weight_small` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The partitions [1], [2], [3], [2,2], [5] and [2,2,2] attain the six displayed values. The same general majorant supplies their upper bounds.

**Theorem 1.5 (The factorial maximum).**

$$\forall n \in Nat,\; 7 \le n \Rightarrow (\operatorname{maximumWeight}\left(n\right) = n!)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.maximum_weight_eq_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The partition with n parts equal to one has weight n factorial. This lower bound meets the universal upper bound for every n at least seven.

**Theorem 1.6 (Absorbing the remaining dimension).**

$$\forall s \in Nat,\; \forall n \in Nat,\; 1 \le s \Rightarrow (s \le n \Rightarrow (\operatorname{maximumWeight}\left(s\right)\cdot(n-s+1)! \le \operatorname{maximumWeight}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.maximum_weight_mul_factorial_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inequality holds for every pair of positive dimensions s at most n, with the factorial of n minus s plus one. Equality handles s equal to n; s equal to one uses the all-ones lower bound. For the remaining dimensions, compare the maximum in dimension s to n descending factorial of length s minus one and use factorial_mul_descFactorial. This arithmetic statement does not identify a partition of s with a partition of n and makes no assertion about algebra automorphisms.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.maximumWeight`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.maximum_weight_eq_factorial`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.maximum_weight_mul_factorial_le`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.maximum_weight_small`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.weight`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.weight_le_factorial`
