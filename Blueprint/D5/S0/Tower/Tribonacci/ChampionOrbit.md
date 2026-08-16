# Tribonacci Champion Orbit

## Abstract

A closed Tribonacci period-two point has its exact liminf survivor arm.

**Definition 1.1 (Closed form of the period-two point).**

$$\mathit{xc} = \frac{t^{0 - 1} - t^{0 - 2}}{2}$$

*Formalization.* `D5/S0/Tower/Tribonacci/ChampionOrbit.tribonacciChampionPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected point is one half of t inverse minus t inverse squared. It lies in the first level-three large gap and is reused without redefining the frozen Tribonacci constant.

**Theorem 1.2 (The containing gap has period-two itinerary ba).**

$$\forall k \in N,\; \operatorname{IsTribonacciOrbitGap}\left(2 \cdot k + 3, \mathit{xc}, \frac{t^{2} - t}{2}, \frac{1 - t^{0 - 1}}{2}\right) \land \operatorname{IsTribonacciOrbitGap}\left(2 \cdot k + 4, \mathit{xc}, \frac{t - 1}{2}, \frac{t - 1}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/ChampionOrbit.tribonacci_champion_gap_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every odd phase the point occupies a large gap with normalized left coordinate (t squared minus t)/2 and right arm (1-t inverse)/2. Refinement takes the right branch b into a combined gap, where the point is the midpoint; the next left branch a returns to the same large-gap coordinate.

**Theorem 1.3 (Exact low arm on every large-gap phase).**

$$\forall k \in N,\; \operatorname{tribonacciSurvivor}\left(2 \cdot k + 3, \mathit{xc}\right) = \frac{1 - t^{0 - 1}}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/ChampionOrbit.tribonacci_champion_survivor_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized distance on levels 2k+3 is exactly (1-t inverse)/2.

The companion theorem tribonacci_champion_survivor_even gives the intervening level 2k+4 value (t-1)/2.

$$
\forall k \in N,\; \operatorname{tribonacciSurvivor}\left(2 \cdot k + 4, \mathit{xc}\right) = \frac{t - 1}{2}
$$

**Theorem 1.4 (The period-two liminf arm).**

$$\operatorname{liminfAtTop}\left(\operatorname{tribonacciSurvivor}\left(Q, \mathit{xc}\right)\right) = \frac{1 - t^{0 - 1}}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/ChampionOrbit.tribonacci_champion_liminf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every tail value is at least the low phase and odd phases occur cofinally, so the filter liminf is exactly (1-t inverse)/2.

This is an along-level liminf theorem. It neither uses the fixed-level one-half bound as a substitute nor claims the unformalized global supremum over all points.

## References

- Truth anchor: `D5/S0/Tower/Tribonacci/ChampionOrbit.tribonacciChampionPoint`
- Truth anchor: `D5/S0/Tower/Tribonacci/ChampionOrbit.tribonacci_champion_gap_orbit`
- Truth anchor: `D5/S0/Tower/Tribonacci/ChampionOrbit.tribonacci_champion_liminf`
- Truth anchor: `D5/S0/Tower/Tribonacci/ChampionOrbit.tribonacci_champion_survivor_odd`
- Dependency: [D5/S0/Tower/Tribonacci/Substitution](Substitution.md)
- Dependency: [D5/S0/Tower/Tribonacci/Survivor](Survivor.md)
