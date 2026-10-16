# Primitive unary-prefix parsing

## Abstract

Primitive unary-prefix parsing.

The finite parser consumes unary prefix bits into a Boolean counter and leaves the remaining payload unchanged. Missing terminators reject by actual execution. Its exact instruction budget is used by paired input decoding.

**Theorem 1.1 (exec_readUnary_encoded).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackParse.exec_readUnary_encoded`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackParse.exec_readUnary_encoded` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackParse.exec_readUnary_encoded`
- Dependency: [D5/S0/Computability/BinaryMachine/StackWords](StackWords.md)
- Dependency: [D5/S0/Computability/BinaryMachine/UnaryWords](UnaryWords.md)
