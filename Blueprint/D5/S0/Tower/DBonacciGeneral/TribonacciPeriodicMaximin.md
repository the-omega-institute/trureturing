# Tribonacci Periodic Maximin

## Abstract

The complete period-at-most-five enumeration has maximin championValue(t), attained by the period-two ba cycle.

**Theorem 1.1 (Every cycle has a low arm below the champion).**

$$\operatorname{selectedLowArmsBoundedBy}\left(\mathit{tribonacciPeriodicOrbitRepresentativesFive}, \operatorname{championValue}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin.tribonacci_periodic_orbit_low_arms_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A selected state on each of the ten cycles has arm at most the frozen value. All comparisons are exact consequences of the cubic.

**Theorem 1.2 (The champion representative is the ba cycle).**

$$\operatorname{decodedOrbitStates}\left(\mathit{tribonacciChampionPeriodicOrbit}\right) = \operatorname{list}\left(\operatorname{state}\left(\mathit{large}, \frac{t^{2} - t}{2}\right), \operatorname{state}\left(\mathit{combined}, \frac{t - 1}{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin.tribonacci_champion_decoded_orbit_states` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The large-right and combined-left branches decode to the two phase states of the repeating ba itinerary.

**Theorem 1.3 (The ba cycle attains the frozen value).**

$$\operatorname{TribonacciOrbitMinimum}\left(\mathit{tribonacciChampionPeriodicOrbit}, \operatorname{championValue}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin.tribonacci_champion_periodic_orbit_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both phase arms are bounded below by championValue(t), and the large phase attains (1 - t inverse) / 2 exactly.

**Theorem 1.4 (The periodic maximin through five).**

$$\operatorname{IsGreatest}\left(\mathit{tribonacciPeriodicOrbitMinimaFive}, \operatorname{championValue}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin.tribonacci_periodic_orbit_maximin_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every enumerated orbit minimum is at most the champion value, while the period-two ba orbit belongs to the finite family and attains it.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin.tribonacci_champion_decoded_orbit_states`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin.tribonacci_champion_periodic_orbit_minimum`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin.tribonacci_periodic_orbit_low_arms_bounded`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin.tribonacci_periodic_orbit_maximin_five`
- Dependency: [D5/S0/Tower/DBonacciGeneral/ChampionValue](ChampionValue.md)
- Dependency: [D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness](TribonacciPeriodicCompleteness.md)
