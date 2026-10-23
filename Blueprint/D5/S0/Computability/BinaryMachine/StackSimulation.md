# Counted stack-to-tape simulation

## Abstract

Counted stack-to-tape simulation.

The finite controller implements each stack instruction through physical tape macros. A room invariant bounds every live register by a shared capacity. Summing the per-instruction budgets gives a polynomial tape execution bound and preserves either halting decision.

**Theorem 1.1 (controller_simulates).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackSimulation.controller_simulates`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackSimulation.controller_simulates` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackSimulation.controller_simulates`
- Dependency: [D5/S0/Computability/BinaryMachine/StackCompiler](StackCompiler.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackEncoding](StackEncoding.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackPop](StackPop.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackProgram](StackProgram.md)
- Dependency: [D5/S0/Computability/BinaryMachine/TapeEquiv](TapeEquiv.md)
