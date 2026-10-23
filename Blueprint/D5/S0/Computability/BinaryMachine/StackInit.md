# Initialization of encoded Boolean registers

## Abstract

Initialization of encoded Boolean registers.

A fixed tape program transforms the literal input tape into the marked register representation with all other stacks empty. Its complete run and cell layout supply the initialization part of the same-model stack compiler.

**Theorem 1.1 (initMachine_run).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackInit.initMachine_run`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackInit.initMachine_run` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackInit.initMachine_run`
- Dependency: [D5/S0/Computability/BinaryMachine/StackCompiler](StackCompiler.md)
- Dependency: [D5/S0/Computability/BinaryMachine/TapeEquiv](TapeEquiv.md)
