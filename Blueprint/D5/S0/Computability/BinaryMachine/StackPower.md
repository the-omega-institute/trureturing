# Executed unary polynomial budgets

## Abstract

Executed unary polynomial budgets.

Register two holds the unary base and register three holds the accumulator. Multiplication repeats a copy-and-transfer of the preserved base once for each accumulator bit. A fixed finite sequence of these multiplications computes c times n to the e, starting from literal c. All work stacks are restored, the two input frame registers are preserved, and the full exact instruction recurrence has a polynomial envelope. Zero coefficients, zero exponents and empty unary bases are included.

**Theorem 1.1 (exec_multiply).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackPower.exec_multiply`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackPower.exec_multiply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

Register two holds the unary base and register three holds the accumulator. Multiplication repeats a copy-and-transfer of the preserved base once for each accumulator bit. A fixed finite sequence of these multiplications computes c times n to the e, starting from literal c. All work stacks are restored, the two input frame registers are preserved, and the full exact instruction recurrence has a polynomial envelope. Zero coefficients, zero exponents and empty unary bases are included.

**Theorem 1.2 (exec_power).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackPower.exec_power`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackPower.exec_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

Register two holds the unary base and register three holds the accumulator. Multiplication repeats a copy-and-transfer of the preserved base once for each accumulator bit. A fixed finite sequence of these multiplications computes c times n to the e, starting from literal c. All work stacks are restored, the two input frame registers are preserved, and the full exact instruction recurrence has a polynomial envelope. Zero coefficients, zero exponents and empty unary bases are included.

**Theorem 1.3 (polynomialBound_time).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackPower.polynomialBound_time`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackPower.polynomialBound_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

Register two holds the unary base and register three holds the accumulator. Multiplication repeats a copy-and-transfer of the preserved base once for each accumulator bit. A fixed finite sequence of these multiplications computes c times n to the e, starting from literal c. All work stacks are restored, the two input frame registers are preserved, and the full exact instruction recurrence has a polynomial envelope. Zero coefficients, zero exponents and empty unary bases are included.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackPower.exec_multiply`
- Truth anchor: `D5/S0/Computability/BinaryMachine/StackPower.exec_power`
- Truth anchor: `D5/S0/Computability/BinaryMachine/StackPower.polynomialBound_time`
- Dependency: [D5/S0/Computability/BinaryMachine/PolynomialBound](PolynomialBound.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackControl](StackControl.md)
