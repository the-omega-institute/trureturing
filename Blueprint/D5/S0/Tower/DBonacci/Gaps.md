# D-Bonacci Gaps

## Abstract

The level-Q d-bonacci name values have exactly min(d,Q) adjacent lengths.

A joint induction follows the finite run budget. A false prefix returns to full budget, a true prefix spends one unit, and the boundary between the two blocks is the scaled terminal gap of the full-budget layer.

**Theorem 1.1 (Consecutive d-bonacci gap).**

$$\forall d \in N,\; \forall Q \in N,\; \operatorname{gapLabelExists}\left(d, Q, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Gaps.consecutive_nameValue_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every consecutive difference is beta_d^-Q times the first f+1 reciprocal powers, for a label f in the interval [d-Q,d).

**Theorem 1.2 (Indexed d-bonacci values increase strictly).**

$$\forall d \in N,\; \forall Q \in N,\; \operatorname{StrictMono}\left(\operatorname{indexedNameValue}\left(d, Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Gaps.indexed_nameValue_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every candidate is a positive power times a positive reciprocal-power sum, so positivity of adjacent steps yields strict monotonicity.

**Theorem 1.3 (Exact d-bonacci gap spectrum).**

$$\forall d \in N,\; \forall Q \in N,\; \operatorname{adjacentGapSpectrum}\left(d, Q\right) = \operatorname{gapLengthImage}\left(\operatorname{Ico}\left(d + \operatorname{neg}\left(Q\right), d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Gaps.adjacent_gap_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All adjacent gaps lie in the stated interval image. Conversely, each new endpoint label is realized at a prefix-block boundary and persists inside the zero-prefix block.

**Theorem 1.4 (D-bonacci gap spectrum cardinality).**

$$\forall d \in N,\; \forall Q \in N,\; \operatorname{card}\left(\operatorname{adjacentGapSpectrum}\left(d, Q\right)\right) = \operatorname{min}\left(d, Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Gaps.adjacent_gap_spectrum_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reciprocal-prefix sums are strictly increasing in their labels. Thus the interval image has min(d,Q) distinct elements, and the full d-gap spectrum occurs exactly when d is at most Q.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/Gaps.adjacent_gap_spectrum`
- Truth anchor: `D5/S0/Tower/DBonacci/Gaps.adjacent_gap_spectrum_card`
- Truth anchor: `D5/S0/Tower/DBonacci/Gaps.consecutive_nameValue_gap`
- Truth anchor: `D5/S0/Tower/DBonacci/Gaps.indexed_nameValue_strictMono`
- Dependency: [D5/S0/Tower/DBonacci/Values](Values.md)
