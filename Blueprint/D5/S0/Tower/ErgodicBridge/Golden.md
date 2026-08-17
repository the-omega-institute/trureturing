# Golden Ergodic Bridge

## Abstract

Golden name-grid liminf is exactly the lower arm value of an expanding gap orbit.

The observable is the nearer normalized gap arm. It is compared by liminf, not by a Birkhoff average: at every refinement level it equals the name-grid survivor, and on a periodic orbit its liminf is the orbit minimum.

The carrier is the internal name-grid hull. The omitted right terminal point has a one-sided terminal gap and is not a state of this two-ended expanding map.

**Theorem 1.1 (Every internal grid point has an equal orbit value).**

$$\forall Q0 \in N, x \in R,\; \left(\mathit{Q0} \ge 2 \land x \in \operatorname{goldenNameHull}\left(\mathit{Q0}\right)\right) \Rightarrow \left(\exists state \in \mathit{GoldenSurvivorState},\; \operatorname{GoldenUnitState}\left(\mathit{state}\right) \land \operatorname{liminf}\left(\operatorname{goldenSurvivorLevels}\left(x\right)\right) = \operatorname{goldenOrbitLowerValue}\left(\mathit{state}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/Golden.golden_ergodic_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every starting level at least two and every point in its internal name-grid hull, a unit gap state codes the point. Gap substitution preserves that coding, so the two liminf values are equal after discarding the finite initial prefix.

**Theorem 1.2 (Every unit state has an internal grid realization).**

$$\forall state \in \mathit{GoldenSurvivorState},\; \operatorname{GoldenUnitState}\left(\mathit{state}\right) \Rightarrow \left(\exists x \in R,\; x \in \operatorname{goldenNameHull}\left(2\right) \land \operatorname{liminf}\left(\operatorname{goldenSurvivorLevels}\left(x\right)\right) = \operatorname{goldenOrbitLowerValue}\left(\mathit{state}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/Golden.golden_ergodic_bridge_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A certified large gap and small gap at level two realize every coordinate in the unit interval. Thus the dynamical state space introduces no extra lower values absent from the internal name-grid problem.

**Theorem 1.3 (Grid and orbit lower-value sets are equal).**

$$\mathit{goldenGridLowerValues} = \mathit{goldenErgodicLowerValues}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/Golden.golden_lower_value_sets_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward and reverse realizations identify the full sets of attained lower asymptotic values, rather than only the known champion point.

**Theorem 1.4 (The golden champion objective is ergodic optimization).**

$$\mathit{goldenGridOptimalValue} = \mathit{goldenErgodicOptimalValue}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/Golden.golden_optimal_value_eq_ergodic_optimal_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the supremum of the equal value sets turns the internal name-grid champion objective into maximin optimization of the lower arm observable on the piecewise linear expanding map.

## References

- Truth anchor: `D5/S0/Tower/ErgodicBridge/Golden.golden_ergodic_bridge`
- Truth anchor: `D5/S0/Tower/ErgodicBridge/Golden.golden_ergodic_bridge_reverse`
- Truth anchor: `D5/S0/Tower/ErgodicBridge/Golden.golden_lower_value_sets_eq`
- Truth anchor: `D5/S0/Tower/ErgodicBridge/Golden.golden_optimal_value_eq_ergodic_optimal_value`
- Dependency: [D5/S0/Tower/Champions/GoldenAsymptotic](../Champions/GoldenAsymptotic.md)
- Dependency: [D5/S0/Tower/Champions/GoldenSurvivorTubes](../Champions/GoldenSurvivorTubes.md)
