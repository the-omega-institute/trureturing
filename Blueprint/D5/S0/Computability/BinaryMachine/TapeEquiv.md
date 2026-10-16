# Blank-padding equivalence of tape execution

## Abstract

Blank-padding equivalence of tape execution.

Tape equivalence compares the bi-infinite tape modulo irrelevant trailing blanks. It preserves the current read symbol, each write and move, output bytes and halting executions. A finite representation with extra blank storage therefore supports the same physical computation.

**Theorem 1.1 (run_some_of_equivalent).**

Lean statement: `D5/S0/Computability/BinaryMachine/TapeEquiv.run_some_of_equivalent`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/TapeEquiv.run_some_of_equivalent` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/TapeEquiv.run_some_of_equivalent`
- Dependency: [D5/S0/Computability/BinaryMachine/Machine](Machine.md)
