# Finite Boolean stack machines

## Abstract

Finite Boolean stack machines.

Every instruction is a literal push, pop, peek, jump or halt on one of finitely many Boolean stacks. A register initially bounded by input length grows by at most one bit per instruction. This supplies an executed size bound for malformed decoder residuals.

**Theorem 1.1 (runInput_length_le).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackMachine.runInput_length_le`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackMachine.runInput_length_le` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackMachine.runInput_length_le`
- Dependency: [D5/S0/Computability/BinaryMachine/Machine](Machine.md)
