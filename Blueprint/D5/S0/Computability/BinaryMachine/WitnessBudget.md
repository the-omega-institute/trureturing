# Checking the original target certificate bound

## Abstract

Checking the original target certificate bound.

For an arbitrary target x and witness w, the finite program computes unary length(x) plus one, constructs c times that base to exponent e, and compares length(w) to it. The target bytes are preserved and work registers are empty on return. Runtime and residual stack bounds are polynomial in the actual target and witness lengths, including c equal to zero and e equal to zero.

**Theorem 1.1 (exec_test).**

Lean statement: `D5/S0/Computability/BinaryMachine/WitnessBudget.exec_test`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/WitnessBudget.exec_test` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

For an arbitrary target x and witness w, the finite program computes unary length(x) plus one, constructs c times that base to exponent e, and compares length(w) to it. The target bytes are preserved and work registers are empty on return. Runtime and residual stack bounds are polynomial in the actual target and witness lengths, including c equal to zero and e equal to zero.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/WitnessBudget.exec_test`
- Dependency: [D5/S0/Computability/BinaryMachine/StackCompare](StackCompare.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackPair](StackPair.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackPower](StackPower.md)
