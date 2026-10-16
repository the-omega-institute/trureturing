# Complexity classes in one concrete machine model

## Abstract

Complexity classes in one concrete machine model.

PolyTime requires one actual total tape transducer that halts true and writes the specified output on every raw binary word. NP uses a total polynomial-time decision machine on the exact pairWords instance and witness bytes, with a uniform polynomial witness bound. PolyRed is a total deterministic polynomial many-one reduction.

**Definition 1.1 (NPComplete).**

Lean statement: `D5/S0/Computability/BinaryMachine/Classes.NPComplete`

*Formalization.* `D5/S0/Computability/BinaryMachine/Classes.NPComplete` (`✓ std3`).

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/Classes.NPComplete`
- Dependency: [D5/S0/Computability/BinaryMachine/Machine](Machine.md)
