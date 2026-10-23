# Whole stack programs as polynomial tape machines

## Abstract

Whole stack programs as polynomial tape machines.

Initialization, controller simulation and output extraction form one tape machine. A proved polynomial bound on every stack run yields a polynomial tape transducer; total runs with either decision yield a total decision machine. Determinism reflects acceptance as well as preserving it.

**Theorem 1.1 (polyTime_of_stack).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackCompile.polyTime_of_stack`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackCompile.polyTime_of_stack` (`✓ std3`). ∎

*Citation.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

This declaration and its proof are attributed immutable source supply. The mathematical namespace and proof body are preserved. Full license, source correspondence and the finite retirement contract are recorded in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies no new classification or independent mathematical escape content.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackCompile.polyTime_of_stack`
- Dependency: [D5/S0/Computability/BinaryMachine/PolynomialBound](PolynomialBound.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackInit](StackInit.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackSimulation](StackSimulation.md)
