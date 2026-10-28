# Tape execution inside finite stacks

## Abstract

Tape execution inside finite stacks.

The tape model is encoded into three Boolean registers using a fixed two-bit symbol representation. The core simulation preserves both accepting and rejecting decisions. A separate normalized transducer extracts exactly the physical output on true halts and restores its two work registers.

**Theorem 1.1 (simulate_core).**

Lean statement: `D5/S0/Computability/BinaryMachine/TapeToStacks.simulate_core`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/TapeToStacks.simulate_core` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/TapeToStacks.simulate_core`
- Dependency: [D5/S0/Computability/BinaryMachine/StackSimulation](StackSimulation.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackWords](StackWords.md)
