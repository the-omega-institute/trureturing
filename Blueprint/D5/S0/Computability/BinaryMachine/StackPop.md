# Physical stack deletion

## Abstract

Physical stack deletion.

Deleting a stack head uses the supplied tape deletion and shifting machines. The representation relates the entire remaining encoded register region and both neighboring regions; output projection is taken from the actual final tape.

**Theorem 1.1 (pop_register_of_equivalent).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackPop.pop_register_of_equivalent`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackPop.pop_register_of_equivalent` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackPop.pop_register_of_equivalent`
- Dependency: [D5/S0/Computability/BinaryMachine/StackCompiler](StackCompiler.md)
- Dependency: [D5/S0/Computability/BinaryMachine/TapeEquiv](TapeEquiv.md)
