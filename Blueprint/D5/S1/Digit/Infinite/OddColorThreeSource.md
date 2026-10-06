# Odd color words and actual periodic sources

## Abstract

Odd color words and actual periodic sources.

**Theorem 1.1 (At most two sources for an odd color word).**

Lean statement: `D5/S1/Digit/Infinite/OddColorThreeSource.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/OddColorThreeSource.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let beta be strictly below lambda and let m be a positive odd integer. For every word of m original closed colors, the set of actual legal addresses with a window period dividing m and with the prescribed closed color at every time has extended cardinality at most two. The coordinates are the literal kappa values after each three-bit deletion.

An address with an odd bit period cannot have a finite return-block prefix followed by the nonconstant alternating endpoint tail. The signed-series fiber classification therefore makes its scalar encoding unique. Periodicity also makes deletion injective among these addresses, so three distinct sources would have three distinct scalar values at every time.

Each closed color allows two adjacent root branches, with only one branch available where the other does not meet the color. Below the critical budget, the color width is strictly smaller than the translation difference. Thus the two root groups retain their order after inverse iteration, including closed endpoints, while every single branch reverses the order within its group.

For three distinct values, either all three belong to one root group or one group contains two values and the other contains one. Both cases reverse sorting parity. The exclusive-or of the three strict pair comparisons records this parity. It changes at every step, has period two, and changes over m steps because m is odd. Each periodic address returns coordinatewise after m steps, forcing the same parity and giving a contradiction.

## References

- Truth anchor: `D5/S1/Digit/Infinite/OddColorThreeSource.result`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationGraphRealization](ClosedObservationGraphRealization.md)
