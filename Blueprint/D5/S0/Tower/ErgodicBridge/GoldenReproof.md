# Golden General-Bridge Reproof

## Abstract

The frozen golden optimum is reproved by the general Fin-d ergodic bridge.

The two frozen gap-geometry laws supply a Fin 2 instance of the general bridge. The instance is separate from the frozen golden module.

**Theorem 1.1 (The golden optimum follows from the general bridge).**

$$\mathit{goldenGridOptimalValue} = \mathit{goldenErgodicOptimalValue}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/GoldenReproof.golden_general_bridge_optimal_value_reproved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old grid and orbit value sets are identified with the general instance sets. General optimality then proves the same equality without invoking the frozen optimality theorem.

## References

- Truth anchor: `D5/S0/Tower/ErgodicBridge/GoldenReproof.golden_general_bridge_optimal_value_reproved`
- Dependency: [D5/S0/Tower/ErgodicBridge/General](General.md)
- Dependency: [D5/S0/Tower/ErgodicBridge/Golden](Golden.md)
