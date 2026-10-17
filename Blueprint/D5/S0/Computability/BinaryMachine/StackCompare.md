# A total primitive witness-length comparison

## Abstract

A total primitive witness-length comparison.

A four-state finite program pops one source and one budget bit for each match. It returns true exactly when source length is at most budget length, irrespective of the bit values. Its actual instruction count is bounded by twice the source length plus three. Every other register remains unchanged.

**Theorem 1.1 (exec_check).**

Lean statement: `D5/S0/Computability/BinaryMachine/StackCompare.exec_check`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/StackCompare.exec_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

A four-state finite program pops one source and one budget bit for each match. It returns true exactly when source length is at most budget length, irrespective of the bit values. Its actual instruction count is bounded by twice the source length plus three. Every other register remains unchanged.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/StackCompare.exec_check`
- Dependency: [D5/S0/Computability/BinaryMachine/StackControl](StackControl.md)
