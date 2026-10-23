# Executed polynomial transducer composition

## Abstract

Executed polynomial transducer composition.

The first tape transducer is simulated and normalized to its exact output word before the second runs. Physical output size bounds the second input. Actual counted stack and tape simulations establish composition for total true-halting transducers.

**Theorem 1.1 (PolyTime.comp).**

Lean statement: `D5/S0/Computability/BinaryMachine/Composition.comp`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/Composition.comp` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/Composition.comp`
- Dependency: [D5/S0/Computability/BinaryMachine/PolynomialBound](PolynomialBound.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackCompile](StackCompile.md)
- Dependency: [D5/S0/Computability/BinaryMachine/TapeToStacks](TapeToStacks.md)
