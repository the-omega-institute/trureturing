# Word Counts and Coefficient Capacity

## Abstract

Word counts, parity cancellation and coefficient capacity for common priority prediction.

Window is the five-symbol alphabet zero, low, middle, ends, high. The two endpoint bits are first and last. A rare symbol is low, ends or high; rareN counts rare symbols, and highN counts high endpoints in a prefix. All words are admitted, with no seam conditioning.

The bivariate generating polynomial records both rare symbols and high endpoints. The slice with k high endpoints is choose(n,k) times (2X)^k times (2+X)^(n-k). The parity of the number of ends symbols supplies a coin. On every positive high-endpoint slice, fixing any one endpoint bit leaves equal polynomial weights for the two coin values.

A reduced word has a prefix of length m and three anchors. The reservoir requires its first anchor to be zero, middle or high, its second anchor to be high, and its third anchor to be low or ends. Every left-layer teacher has label zero there and every right-layer teacher has label two. Nz(m,z) counts reservoir words with exactly z rare symbols.

The binomial weights choose(j,k) times 2 to the k have total 3 to the j and first moment 2j times 3 to the j-1. The truncated tail at floor(m/3) satisfies a strengthened moment estimate and grows by at least a factor of three when the degree increases. These relations bound the signed discrepancy coefficients on both sides by the reservoir coefficients, including m=1 and m=2.

The majority selector compares all three vote counts and uses a coin on tied choices. Its eight regions cover every prefix endpoint count, and the selected label maximizes votes throughout each region. These finite comparisons apply to both coin values.

**Theorem 1.1 (Integer reservoir capacity).**

$$\forall \left(m: Nat\right), \forall \left(z: Nat\right), \left(0 < m\right) \implies \left(\exists \left(t: Nat\right), \left(\operatorname{int}\left(t\right) \le 2\cdot\operatorname{reservoirHalf}\left(m, z\right)\right) \land \left(2\cdot\operatorname{discrepancyHalf}\left(m, z\right)-2\cdot\operatorname{reservoirHalf}\left(m, z\right)+2\cdot\operatorname{int}\left(t\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.integer_split_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reservoir and discrepancy half coefficients are integers. Their two-sided bound makes the half difference a nonnegative integer, at most the complete reservoir coefficient. This supplies a legal split size in every rare-count class. Prefix and anchor generating functions identify the coefficients with actual word counts.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.integer_split_positive`
- Dependency: [D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation](../HeterogeneousTeacherSeparation.md)
