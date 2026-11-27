# The coefficient kernel for four and three factors

## Abstract

The coefficient kernel for four and three factors

**Theorem 1.1 (Cyclic identity in cube-root variables).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV43Kernel.defect43_eq_cyclic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV43Kernel.defect43_eq_cyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A polynomial identity assigns the quartic trace coefficient to the three centers. The terms agree at zero eigenvalues after evaluating the kernel there.

**Theorem 1.2 (Positivity of the coefficient matrix).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV43Kernel.centeredKernel43_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV43Kernel.centeredKernel43_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Four polynomial features give the Gram term. A diagonal congruence of a Cauchy matrix gives the other term.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV43Kernel.centeredKernel43_psd`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV43Kernel.defect43_eq_cyclic`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVKernel](RefinedBMVKernel.md)
