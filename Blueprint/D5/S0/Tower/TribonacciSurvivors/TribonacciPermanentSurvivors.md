# Tribonacci Permanent Survivors

## Abstract

Strict Tribonacci permanent survival is empty, while the strict one-step domain and a closed period-two permanent carrier are nonempty.

The deterministic three-gap map is expanding. A permanently strict state must enter the large-to-combined two-step branch. Backward comparison with the reciprocal-square contraction then forces the unique boundary period-two orbit, whose large phase is excluded by the strict threshold.

**Theorem 1.1 (The strict permanent survivor set is empty).**

$$\mathit{tribonacciStrictPermanentSet} = \mathit{emptySet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciSurvivors/TribonacciPermanentSurvivors.tribonacci_strict_permanent_set_eq_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is an all-depth intersection statement: no state survives every finite backward depth. It does not assert that the finite-depth survivor at depth 60 is empty.

**Theorem 1.2 (The strict one-step survivor domain is nonempty).**

$$\exists s \in \mathit{TribonacciPeriodicState},\; s \in \mathit{tribonacciStrictSurvivorSet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciSurvivors/TribonacciPermanentSurvivors.tribonacci_strict_survivor_set_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The combined-gap midpoint lies strictly above the threshold. Permanent emptiness is therefore not a vacuous consequence of an empty initial domain.

**Theorem 1.3 (The closed champion carrier survives permanently).**

$$\forall s \in \mathit{TribonacciPeriodicState},\; \operatorname{IsTribonacciClosedChampionState}\left(s\right) \Rightarrow \left(\forall n \in N,\; s \in \operatorname{tribonacciBackwardSurvivor}\left(\mathit{tribonacciClosedSurvivorSet}, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciSurvivors/TribonacciPermanentSurvivors.tribonacci_closed_champion_carrier_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The large and combined champion states form a closed period-two orbit. Their inclusion is a proved lower bound for the closed permanent set, not a classification or an equality.

## References

- Truth anchor: `D5/S0/Tower/TribonacciSurvivors/TribonacciPermanentSurvivors.tribonacci_closed_champion_carrier_subset`
- Truth anchor: `D5/S0/Tower/TribonacciSurvivors/TribonacciPermanentSurvivors.tribonacci_strict_permanent_set_eq_empty`
- Truth anchor: `D5/S0/Tower/TribonacciSurvivors/TribonacciPermanentSurvivors.tribonacci_strict_survivor_set_nonempty`
- Dependency: [D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin](../DBonacciGeneral/TribonacciPeriodicMaximin.md)
