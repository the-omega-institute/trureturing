# Physical tape insertion and deletion

## Abstract

Physical tape insertion and deletion.

Literal tape machines insert, shift and delete cells and rewind to a marked boundary. Their counted runs provide the physical operations used by the stack compiler; tape capacity is charged through actual scans rather than output length alone.

**Theorem 1.1 (insert_run).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackCompiler.insert_run`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackCompiler.insert_run` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackCompiler.insert_run`
- Dependency: [D5/S0/Computability/BinaryMachine/StackMachine](StackMachine.md)
