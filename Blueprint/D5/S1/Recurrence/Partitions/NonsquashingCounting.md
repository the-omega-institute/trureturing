# Counting Distinct Non-Squashing Partitions

## Abstract

Deleting the largest part proves the Sloane--Sellers recurrence for distinct non-squashing partitions.

Write P(n) for nonsquashingDistinctPartitions(n) and B(n) for its cardinality. Every part is a positive natural number. A finite set represents distinct parts; in decreasing order, the smaller parts are precisely the suffix. Equality between a part and its suffix sum is allowed. The empty partition contributes B(0)=1.

**Definition 1.1 (The direct finite partition family).**

$$\forall n: \mathbb{N}, \operatorname{P}\left(n\right) = \operatorname{filter}\left(\operatorname{powerset}\left(\operatorname{Icc}\left(1, n\right)\right), (s \mapsto \operatorname{sum}\left(s\right) = n \land \forall p \in s, \operatorname{sum}\left(\operatorname{filter}\left(s, (q \mapsto q < p)\right)\right) \leq p)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/NonsquashingCounting.nonsquashingDistinctPartitions` (`✓ std3`).

*Citation.* N. J. A. Sloane; James A. Sellers (2003). *On Non-Squashing Partitions*. DOI: [10.48550/arXiv.math/0312418](https://doi.org/10.48550/arXiv.math/0312418).

*Commentary.*

Take the powerset of the inclusive interval from one through n, and retain exactly the sets whose sum is n and whose smaller-part sum never exceeds the part. This definition is independent of every recurrence proved below.

**Theorem 1.2 (The odd-index increment).**

$$\forall m: \mathbb{N}, 0 < m \Rightarrow \operatorname{B}\left(2 \cdot m + 1\right) = \operatorname{B}\left(2 \cdot m\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/NonsquashingCounting.count_odd` (`✓ std3`). ∎

*Citation.* N. J. A. Sloane; James A. Sellers (2003). *On Non-Squashing Partitions*. DOI: [10.48550/arXiv.math/0312418](https://doi.org/10.48550/arXiv.math/0312418).

*Commentary.*

Adjoin 2m+1-j to a partition of j for each j from zero through m. The new part exceeds the entire tail sum, so this is a bijection. For 2m the same construction excludes exactly the singleton tail {m}. Deleting the largest part gives the inverse, and removing that one tail accounts for the difference of one. The condition m>0 is essential; the printed unrestricted odd rule in Corollary 4 fails at n=1.

**Theorem 1.3 (Successive even indices).**

$$\forall m: \mathbb{N}, 0 < m \Rightarrow \operatorname{B}\left(2 \cdot (m + 1)\right) = \operatorname{B}\left(2 \cdot m\right) + \operatorname{B}\left(m + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/NonsquashingCounting.count_even_step` (`✓ std3`). ∎

*Citation.* N. J. A. Sloane; James A. Sellers (2003). *On Non-Squashing Partitions*. DOI: [10.48550/arXiv.math/0312418](https://doi.org/10.48550/arXiv.math/0312418).

*Commentary.*

Theorem 2's cumulative formula says B(2m)+1 is the sum of B(j) for zero through m. Subtract the two consecutive cumulative identities. Only B(m+1) remains, giving this equivalent positive-even recurrence.

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/NonsquashingCounting.count_even_step`
- Truth anchor: `D5/S1/Recurrence/Partitions/NonsquashingCounting.count_odd`
- Truth anchor: `D5/S1/Recurrence/Partitions/NonsquashingCounting.nonsquashingDistinctPartitions`
