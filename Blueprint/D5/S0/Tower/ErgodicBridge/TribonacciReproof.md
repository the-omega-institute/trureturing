# Tribonacci General-Bridge Reproof

## Abstract

The frozen Tribonacci optimum is reproved by the general Fin-d ergodic bridge.

The three frozen gap-geometry laws supply a Fin 3 instance of the general bridge. The instance is separate from the frozen Tribonacci module.

**Theorem 1.1 (The Tribonacci optimum follows from the general bridge).**

$$\mathit{tribonacciGridOptimalValue} = \mathit{tribonacciErgodicOptimalValue}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ErgodicBridge/TribonacciReproof.tribonacci_general_bridge_optimal_value_reproved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old grid and orbit value sets are identified with the general instance sets. General optimality then proves the same equality without invoking the frozen optimality theorem.

## References

- Truth anchor: `D5/S0/Tower/ErgodicBridge/TribonacciReproof.tribonacci_general_bridge_optimal_value_reproved`
- Dependency: [D5/S0/Tower/ErgodicBridge/General](General.md)
- Dependency: [D5/S0/Tower/ErgodicBridge/Tribonacci](Tribonacci.md)
