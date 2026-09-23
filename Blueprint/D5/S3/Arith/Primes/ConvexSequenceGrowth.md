# Growth of convex integer sequences

## Abstract

A strictly increasing integer sequence with nondecreasing gaps outgrows every multiple of n squared exactly when its gaps outgrow every multiple of n.

Nondecreasing consecutive gaps make the growth of a sequence and the growth of its gaps two readings of one fact: the sequence is a partial sum of the gaps, and monotonicity turns that sum into a two-sided estimate by a single gap. The equivalence below records the exchange rate, which is one power of the index.

**Definition 1.1 (The gap).**

Lean statement: `D5/S3/Arith/Primes/ConvexSequenceGrowth.gap`

*Formalization.* `D5/S3/Arith/Primes/ConvexSequenceGrowth.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a sequence of naturals, gap q n is the difference of the term at n plus one from the term at n, taken in the naturals. Under the strict monotonicity assumed below the subtraction is never truncated.

**Definition 1.2 (Convex sequences).**

Lean statement: `D5/S3/Arith/Primes/ConvexSequenceGrowth.ConvexSequence`

*Formalization.* `D5/S3/Arith/Primes/ConvexSequenceGrowth.ConvexSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A sequence of naturals is convex when it is strictly monotone and each gap is at most its successor. No further arithmetic property is assumed; in particular the terms are not required to be prime.

**Theorem 1.3 (The equivalence).**

Lean statement: `D5/S3/Arith/Primes/ConvexSequenceGrowth.quotient_tendsto_atTop_iff_gap_tendsto_atTop`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ConvexSequenceGrowth.quotient_tendsto_atTop_iff_gap_tendsto_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a convex sequence q, the real quotient of q n by n squared tends to infinity if and only if the quotient of gap q n by n does. From the gaps to the sequence: monotone gaps give the tail estimate that the term at m plus t is at least the term at m plus t times the gap at m; taking m to be half of n yields a fixed positive multiple of the gap at m divided by m as a lower bound for the quotient at n, and the half-index map itself tends to infinity. From the sequence to the gaps: the same tail estimate read upwards bounds the term at n by the initial term plus n times the gap at n, so the quotient at n is at most the initial term divided by n squared plus the gap quotient; the first summand is eventually at most one, so divergence of the quotient forces divergence of the gap quotient.

## References

- Truth anchor: `D5/S3/Arith/Primes/ConvexSequenceGrowth.ConvexSequence`
- Truth anchor: `D5/S3/Arith/Primes/ConvexSequenceGrowth.gap`
- Truth anchor: `D5/S3/Arith/Primes/ConvexSequenceGrowth.quotient_tendsto_atTop_iff_gap_tendsto_atTop`
