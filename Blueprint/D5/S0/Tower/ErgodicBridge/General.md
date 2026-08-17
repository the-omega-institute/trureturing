# General D-Bonacci Ergodic Bridge

## Abstract

A Fin-d typed coding identifies d-bonacci grid and ergodic lower-value optima.

The changing gap spectrum is represented by the existing Fin d alphabet. Each instance supplies its gap extents, coding transition, and one grid realization uniformly for every letter.

The general proof then iterates the coding, removes the finite prefix in the liminf, proves both realization directions, and compares the two attained-value sets.

**Theorem 1.1 (General grid and orbit lower-value sets are equal).**

$$\forall d \in N, bridge \in \mathit{DBonacciErgodicBridge},\; d \ge 2 \Rightarrow \operatorname{gridLowerValues}\left(\mathit{bridge}\right) = \operatorname{ergodicLowerValues}\left(\mathit{bridge}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/General.lower_value_sets_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Forward coding maps every admissible grid value to a unit orbit. The Fin d realization family maps every unit orbit value back to the fixed realization level.

**Theorem 1.2 (The general d-bonacci objective is ergodic optimization).**

$$\forall d \in N, bridge \in \mathit{DBonacciErgodicBridge},\; d \ge 2 \Rightarrow \operatorname{gridOptimalValue}\left(\mathit{bridge}\right) = \operatorname{ergodicOptimalValue}\left(\mathit{bridge}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/General.optimal_value_eq_ergodic_optimal_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking suprema of the equal attained-value sets identifies the grid champion objective with maximin optimization of the state arm.

## References

- Truth anchor: `D5/S0/Tower/ErgodicBridge/General.lower_value_sets_eq`
- Truth anchor: `D5/S0/Tower/ErgodicBridge/General.optimal_value_eq_ergodic_optimal_value`
- Dependency: [D5/S0/Tower/DBonacci/GapAlphabet](../DBonacci/GapAlphabet.md)
