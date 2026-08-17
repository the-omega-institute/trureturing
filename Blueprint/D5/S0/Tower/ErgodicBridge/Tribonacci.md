# Tribonacci Ergodic Bridge

## Abstract

Tribonacci name-grid liminf is exactly the lower arm value of a three-gap orbit.

The observable is the nearer normalized arm in the current small, combined, or large gap. It is compared by liminf, not by a Birkhoff average.

The carrier is the internal name-grid hull. The omitted right terminal point has a one-sided terminal gap and is not a state of the two-ended map.

**Theorem 1.1 (Every internal grid point has an equal three-gap orbit value).**

$$\forall Q0 \in N, x \in R,\; x \in \operatorname{tribonacciNameHull}\left(\mathit{Q0}\right) \Rightarrow \left(\exists state \in \mathit{TribonacciPeriodicState},\; \operatorname{TribonacciUnitState}\left(\mathit{state}\right) \land \operatorname{liminf}\left(\operatorname{tribonacciSurvivorLevels}\left(x\right)\right) = \operatorname{tribonacciOrbitLowerValue}\left(\mathit{state}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/Tribonacci.tribonacci_ergodic_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every internal grid point determines its containing gap letter and arm coordinate. The five refinement branches preserve this coding, so discarding the finite initial prefix identifies the liminf values.

**Theorem 1.2 (Every typed unit state has an internal grid realization).**

$$\forall state \in \mathit{TribonacciPeriodicState},\; \operatorname{TribonacciUnitState}\left(\mathit{state}\right) \Rightarrow \left(\exists x \in R,\; x \in \operatorname{tribonacciNameHull}\left(3\right) \land \operatorname{liminf}\left(\operatorname{tribonacciSurvivorLevels}\left(x\right)\right) = \operatorname{tribonacciOrbitLowerValue}\left(\mathit{state}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/Tribonacci.tribonacci_ergodic_bridge_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Certified small, combined, and large gaps at level three realize every coordinate in their typed state intervals. The dynamical state space therefore contributes no additional lower values.

**Theorem 1.3 (Tribonacci grid and orbit lower-value sets are equal).**

$$\mathit{tribonacciGridLowerValues} = \mathit{tribonacciErgodicLowerValues}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/Tribonacci.tribonacci_lower_value_sets_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward and three-type reverse realizations identify the full sets of attained lower asymptotic values, not only a periodic champion.

**Theorem 1.4 (The Tribonacci champion objective is ergodic optimization).**

$$\mathit{tribonacciGridOptimalValue} = \mathit{tribonacciErgodicOptimalValue}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/Tribonacci.tribonacci_optimal_value_eq_ergodic_optimal_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the supremum of the equal value sets turns the internal name-grid champion objective into optimization of the lower arm observable on the piecewise linear three-gap map.

## References

- Truth anchor: `D5/S0/Tower/ErgodicBridge/Tribonacci.tribonacci_ergodic_bridge`
- Truth anchor: `D5/S0/Tower/ErgodicBridge/Tribonacci.tribonacci_ergodic_bridge_reverse`
- Truth anchor: `D5/S0/Tower/ErgodicBridge/Tribonacci.tribonacci_lower_value_sets_eq`
- Truth anchor: `D5/S0/Tower/ErgodicBridge/Tribonacci.tribonacci_optimal_value_eq_ergodic_optimal_value`
- Dependency: [D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin](../DBonacciGeneral/TribonacciPeriodicMaximin.md)
- Dependency: [D5/S0/Tower/Tribonacci/ChampionOrbit](../Tribonacci/ChampionOrbit.md)
