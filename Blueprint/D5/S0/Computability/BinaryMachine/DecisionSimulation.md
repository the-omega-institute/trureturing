# Both tape decisions in a stack frame

## Abstract

Both tape decisions in a stack frame.

The supplied initializer and core simulator are lifted injectively into registers zero, two and three. For every actual tape halt, accepting or rejecting, the finite program returns the identical Boolean decision in at most six times input length plus executed tape fuel plus one. This supplies decision transport without requiring true-halt output normalization.

**Theorem 1.1 (exec_program).**

Lean statement: `D5/S0/Computability/BinaryMachine/DecisionSimulation.exec_program`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/DecisionSimulation.exec_program` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

The supplied initializer and core simulator are lifted injectively into registers zero, two and three. For every actual tape halt, accepting or rejecting, the finite program returns the identical Boolean decision in at most six times input length plus executed tape fuel plus one. This supplies decision transport without requiring true-halt output normalization.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/DecisionSimulation.exec_program`
- Dependency: [D5/S0/Computability/BinaryMachine/TransducerPair](TransducerPair.md)
