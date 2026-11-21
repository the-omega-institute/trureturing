# The actual one-cycle hit probability

## Abstract

The one-cycle hit probability of the actual marked-cycle law is the sum of its zero-discard term and its normalized positive-discard series.

**Definition 1.1 (Hit of a single actual cycle).**

Lean statement: `D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.hit`

*Formalization.* `D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.hit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a direct terminal, the terminal permutation must occupy the current diagonal. A skew terminal never hits. A direct discard leaves the discrepancy unchanged, while a skew discard increases it by the length of the discarded shape. The event is then checked on the remaining cycle.

**Definition 1.2 (One-cycle hit probability).**

Lean statement: `D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.nextHazard`

*Formalization.* `D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.nextHazard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At integer discrepancy e, nextHazard is the mass of the hit event under the existing actual marked-cycle law. A direct terminal hits when its actual permutation occupies the diagonal at the current discrepancy. A skew terminal cannot hit. A skew discard of length n+1 increases the discrepancy by n+1, whereas a direct discard leaves it unchanged.

**Definition 1.3 (Normalized skew-removal iteration).**

Lean statement: `D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.normalizedSkewIterate`

*Formalization.* `D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.normalizedSkewIterate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zeroth iterate is the actual direct-terminal hit mass. Each application of the operator sums over actual removed shapes. A shape of length n+1 contributes its weight rho^(n+1) divided by b, and its successor is evaluated at e+n+1. The normalization uses the same b as the critical shape law.

Write H(e) for nextHazard(e), O(e) for rawOccupation(e), and U(k,e) for normalizedSkewIterate(k,e). In the formula B is ofReal(b), all arithmetic outside ofReal is in the extended nonnegative reals, and the summation is over all natural numbers, starting at zero.

**Theorem 1.4 (Exact normalized series).**

$$\forall e \in \mathbb{Z},\; \operatorname{H}\left(e\right) = \operatorname{ofReal}\left(\operatorname{O}\left(e\right)\right) + \sum_{r \in \mathbb{N}} (B^{2 \cdot r + 1} \cdot \left(1 + B\right) \cdot \operatorname{U}\left(r + 1, e\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.nextHazard_eq_normalized_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-discard direct terminal contributes exactly ofReal(O(e)). For r at least zero, the starting-skew pattern with 2r+1 discards and the starting-direct pattern with 2r+2 discards each contain r+1 skew removals. The other two parity patterns cannot hit because they end skew.

The fixed-count law reindexes the actual marked-cycle hit event without introducing an independent model. Direct removals contribute their total weight without shifting the discrepancy; the normalized skew operator retains the actual skew-removal length shifts. Pairing the two positive-count patterns gives the coefficient B^(2r+1)(1+B) at U(r+1,e).

The identity holds at every integer discrepancy. It is an exact extended-nonnegative-real series, not a truncation error estimate, a nonlinear occupied-mass comparison, or a statement about marginal discrepancy tails. It is not by itself a conditional probability statement on past cylinders.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.hit`
- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.nextHazard`
- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.nextHazard_eq_normalized_series`
- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.normalizedSkewIterate`
- Dependency: [D5/S1/Words/Patterns/Separable/ActualCycleLaw](ActualCycleLaw.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedComparison](OccupiedComparison.md)
