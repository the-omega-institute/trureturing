# Exact total ordered pair decoding

## Abstract

Exact total ordered pair decoding.

The outer format is a unary prefix of the first payload length, zero, first payload, then second payload. Decoding succeeds exactly on pairWords x y. The actual unpack program handles every raw word in at most four times its length plus eight instructions; success returns the two unchanged payloads in separate registers.

**Theorem 1.1 (decodePair_eq_some_iff).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackPair.decodePair_eq_some_iff`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackPair.decodePair_eq_some_iff` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackPair.decodePair_eq_some_iff`
- Dependency: [D5/S0/Computability/BinaryMachine/Classes](Classes.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackParse](StackParse.md)
