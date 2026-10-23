# An executed ordered pair constructor

## Abstract

An executed ordered pair constructor.

Registers zero and one contain arbitrary raw words u and v. With work registers two and three empty, the finite program writes exactly pairWords u v into register zero and empties register one in seven times length(u) plus four times length(v) plus twelve instructions. Every other register remains unchanged.

**Theorem 1.1 (exec_build).**

Lean statement: `D5/S0/Computability/BinaryMachine/PairConstructor.exec_build`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/PairConstructor.exec_build` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

Registers zero and one contain arbitrary raw words u and v. With work registers two and three empty, the finite program writes exactly pairWords u v into register zero and empties register one in seven times length(u) plus four times length(v) plus twelve instructions. Every other register remains unchanged.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/PairConstructor.exec_build`
- Dependency: [D5/S0/Computability/BinaryMachine/StackControl](StackControl.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackPair](StackPair.md)
