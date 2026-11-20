# Limits of the Rectangle Tail and Point Laws

## Abstract

Uniform bounds and normalized limits for the rectangular first-descent distribution.

**Definition 1.1 (Finite survival function).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For r at most n, the finite tail is the binomial coefficient choose(r + K - 1, K - 1) times the product of (n - j)/(K n - j) over j from zero through r minus one. For r above n the tail is zero.

**Definition 1.2 (Limiting survival function).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.limitTail`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.limitTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The limiting tail at r is choose(r + K - 1, K - 1) divided by K to the power r.

**Definition 1.3 (Limiting point mass).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.limitMass`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.limitMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The limiting mass at r is r times choose(r + K - 1, K - 2) divided by K to the power r + 1.

**Theorem 1.4 (Summable bound independent of width).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail_le_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail_le_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For K at least two, the absolute value of the finite tail has a width-independent bound of one at r = 0 and (3/4) to the power r - 1 for r at least one. The finite tails are nonnegative and no greater than the limiting tails.

**Theorem 1.5 (Limit of each tail).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_finiteTail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_finiteTail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For K at least two and each natural threshold r, the finite tail tends to the limiting tail as n tends to infinity.

**Theorem 1.6 (Normalization of the point law).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.hasSum_limitMass`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.hasSum_limitMass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When K is at least two, the sum over all natural r of the limiting masses is one. The adjacent-tail differences telescope and the limiting tail tends to zero.

**Theorem 1.7 (Sum of the even masses).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.hasSum_even_limitMass`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.hasSum_even_limitMass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For K at least two, the sum of the limiting masses at even indices is (K/(K + 1)) to the power K. Pairing adjacent tails yields the negative binomial series at -1/K.

**Theorem 1.8 (Limit of the alternating tail sum).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_alternating_finiteTail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_alternating_finiteTail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For K at least two, the alternating sum of the finite tails tends to (K/(K + 1)) to the power K. The same summable bound applies at every width.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail_le_bound`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.hasSum_even_limitMass`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.hasSum_limitMass`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.limitMass`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.limitTail`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_alternating_finiteTail`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_finiteTail`
