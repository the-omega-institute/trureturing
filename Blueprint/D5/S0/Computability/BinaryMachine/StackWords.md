# Executed word operations

## Abstract

Executed word operations.

Clear, transfer, scatter, copy and unary length are finite primitive programs. Copy restores the original source word and scratch while replacing the destination. Exact costs include all loop control and terminal instructions, and frame statements retain untouched registers.

**Theorem 1.1 (exec_copy).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackWords.exec_copy`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackWords.exec_copy` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackWords.exec_copy`
- Dependency: [D5/S0/Computability/BinaryMachine/StackProgram](StackProgram.md)
