# Finite program algebra and compilation

## Abstract

Finite program algebra and compilation.

Typed finite control labels are represented by explicit finite encodings. Counted inductive execution compiles to the same number of primitive stack instructions. Sequential composition retains rejection, loops count their control operations, and label embeddings preserve the actual instruction trace.

**Theorem 1.1 (compile_exec).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackProgram.compile_exec`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackProgram.compile_exec` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackProgram.compile_exec`
- Dependency: [D5/S0/Computability/BinaryMachine/StackMachine](StackMachine.md)
