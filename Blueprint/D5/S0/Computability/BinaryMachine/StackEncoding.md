# Boolean register regions on a tape

## Abstract

Boolean register regions on a tape.

Boolean words occupy delimited tape regions. Register update identities preserve the ordered surrounding regions. Initial input encoding and physical output extraction use this exact representation, with no alternate language encoding.

**Theorem 1.1 (homeTape_initial).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackEncoding.homeTape_initial`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackEncoding.homeTape_initial` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackEncoding.homeTape_initial`
- Dependency: [D5/S0/Computability/BinaryMachine/StackCompiler](StackCompiler.md)
