# Golden Gap Frequency

## Abstract

Boundary-completed golden gaps have exact Fibonacci frequencies.

The frozen adjacent gaps are completed by the final interval from the last indexed name value to one. This keeps every counted gap attached to the actual GoldenName tower and includes the terminal refinement tail.

**Definition 1.1 (Boundary-completed full gap).**

Lean statement: `D5/S0/Tower/GoldenGapFrequency.fullGap`

*Formalization.* `D5/S0/Tower/GoldenGapFrequency.fullGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At an internal index this is the frozen consecutive name-value difference; at the final index it is the remaining interval to one.

**Definition 1.2 (Large full-gap count).**

Lean statement: `D5/S0/Tower/GoldenGapFrequency.largeGapCount`

*Formalization.* `D5/S0/Tower/GoldenGapFrequency.largeGapCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite number of boundary-completed gaps equal to the level-Q large golden length.

**Definition 1.3 (Small full-gap count).**

Lean statement: `D5/S0/Tower/GoldenGapFrequency.smallGapCount`

*Formalization.* `D5/S0/Tower/GoldenGapFrequency.smallGapCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite number of boundary-completed gaps equal to the level-Q small golden length.

**Theorem 1.4 (Full-gap counts are Fibonacci).**

$$\forall Q \in N,\; Q \ge 2 \Rightarrow \left(\operatorname{largeGapCount}\left(Q\right) = \operatorname{Fib}\left(Q + 1\right) \land \left(\operatorname{smallGapCount}\left(Q\right) = \operatorname{Fib}\left(Q\right) \land \operatorname{largeGapCount}\left(Q\right) + \operatorname{smallGapCount}\left(Q\right) = \operatorname{card}\left(\operatorname{GoldenName}\left(Q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenGapFrequency.golden_full_gap_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From level two onward the large and small multiplicities are Fib(Q+1) and Fib(Q). The proof uses the frozen golden gap substitution for the internal refinement partition, proves the terminal boundary recurrence, and checks that the two counts sum to the frozen GoldenName cardinality.

**Theorem 1.5 (Large-to-small gap ratio tends to the golden ratio).**

$$\operatorname{limitAtTop}\left(Q, \frac{\operatorname{largeGapCount}\left(Q + 2\right)}{\operatorname{smallGapCount}\left(Q + 2\right)}\right) = \mathit{goldenRatio}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenGapFrequency.golden_gap_frequency_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact count ratio is the shifted consecutive Fibonacci ratio, so the mathlib Fibonacci limit gives the golden ratio. This is an asymptotic frequency statement for tower gap types; it does not assert a champion classification, a pointwise Birkhoff theorem, or a global maximizing-orbit result. Those layers remain deferred.

## References

- Truth anchor: `D5/S0/Tower/GoldenGapFrequency.fullGap`
- Truth anchor: `D5/S0/Tower/GoldenGapFrequency.golden_full_gap_counts`
- Truth anchor: `D5/S0/Tower/GoldenGapFrequency.golden_gap_frequency_ratio`
- Truth anchor: `D5/S0/Tower/GoldenGapFrequency.largeGapCount`
- Truth anchor: `D5/S0/Tower/GoldenGapFrequency.smallGapCount`
- Dependency: [D5/S0/Tower/GoldenSubstitution](GoldenSubstitution.md)
