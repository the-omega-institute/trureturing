# Finite binary tape machines

## Abstract

Finite binary tape machines.

Each machine has finitely many states and reads a finite symbol alphabet. A run counts every local instruction. Two halting runs from the same configuration agree, including their Boolean decision and complete final tape. The output-size theorem bounds physical output by initial word length plus twice the executed instruction count.

**Theorem 1.1 (run_deterministic).**

Lean statement: `D5/S0/Computability/BinaryMachine/Machine.run_deterministic`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/Machine.run_deterministic` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/Machine.run_deterministic`
