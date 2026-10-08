# Odd color words and actual periodic sources

## Abstract

Odd color words and actual periodic sources.

**Lemma 1.1 (Actual root intervals).**

Lean statement: `D5/S1/Digit/Infinite/OddColorThreeSource.root_bounds`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/OddColorThreeSource.root_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual legal source lies in the closed root interval of its first three-bit label. The intervals for labels 3, 0, 5, 2, and 25 are respectively [-1,t-1], [t-1,g], [g,t], [t,2t], and [2t,1+t].

**Lemma 1.2 (Fixed allowed label pairs).**

Lean statement: `D5/S1/Digit/Infinite/OddColorThreeSource.color_labels`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/OddColorThreeSource.color_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every beta strictly below lambda, a legal source in closed color c has one of its two fixed allowed labels. In color order 0 through 5, these pairs are (3,0), (3,0), (0,5), (5,2), (2,25), and (2,25). The branch intervals exclude all other labels.

**Theorem 1.3 (At most two sources for an odd color word).**

Lean statement: `D5/S1/Digit/Infinite/OddColorThreeSource.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/OddColorThreeSource.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let beta be strictly below lambda and let m be a positive odd integer. For every word of m original closed colors, the set of actual legal addresses that return after every m three-bit windows and have the prescribed closed color at every time has extended cardinality at most two. The coordinates are the literal kappa values after each three-bit deletion. Precisely, the period condition says that digit n + 3m equals digit n for every n; this is equivalent to repeating the legal three-bit windows every m steps. The color condition holds at every nonnegative time j, using color j modulo m.

An address with an odd bit period cannot have a finite return-block prefix followed by the nonconstant alternating endpoint tail. The signed-series fiber classification therefore makes its scalar encoding unique. Periodicity also makes deletion injective among these addresses, so three distinct sources would have three distinct scalar values at every time.

Each closed color permits at most two adjacent root branches. Below the critical budget, the color width is strictly smaller than the translation difference. Thus the two root groups retain their order after inverse iteration, including closed endpoints, while every single branch reverses the order within its group.

For three distinct values, either all three belong to one root group or one group contains two values and the other contains one. Both cases reverse sorting parity. The exclusive-or of the three strict pair comparisons records this parity. It changes at every step, has period two, and changes over m steps because m is odd. Each periodic address returns coordinatewise after m steps, forcing the same parity and giving a contradiction.

## References

- Truth anchor: `D5/S1/Digit/Infinite/OddColorThreeSource.color_labels`
- Truth anchor: `D5/S1/Digit/Infinite/OddColorThreeSource.result`
- Truth anchor: `D5/S1/Digit/Infinite/OddColorThreeSource.root_bounds`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationGraphRealization](ClosedObservationGraphRealization.md)
- Dependency: [D5/S1/Digit/Infinite/SignedSeriesFibres](SignedSeriesFibres.md)
- Dependency: [D5/S1/Digit/Infinite/WindowCylinderPartition](WindowCylinderPartition.md)
