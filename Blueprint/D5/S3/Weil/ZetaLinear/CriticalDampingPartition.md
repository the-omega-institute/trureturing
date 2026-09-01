# Critical Damping Partition

## Abstract

A finite reflection-symmetric damping spectrum has equivalent diagonal, centered-exponential, and hyperbolic-cosine partition traces, with a nonnegative defect that vanishes precisely on the critical line.

**Theorem 1.1 (The centered damping partition has a nonnegative critical defect).**

Lean statement: `D5/S3/Weil/ZetaLinear/CriticalDampingPartition.critical_damping_partition_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/CriticalDampingPartition.critical_damping_partition_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite family of real damping rates defines a complex diagonal matrix. Subtracting one half times the identity produces the centered damping operator, while the normalized partition function is the exponential prefactor times the finite heat sum.

The reflection hypothesis is witnessed by a permutation that negates every centered rate. It cancels the odd exponential contribution and identifies the partition with the trace of the matrix hyperbolic cosine.

The resulting partition defect is a finite sum of cosh(x)-1 terms and is nonnegative. At every nonzero scale it vanishes exactly when all damping rates equal one half. The same module proves the finite maximum norm formula and explicit critical and off-line three-point witnesses.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/CriticalDampingPartition.critical_damping_partition_certificate`
- Dependency: [D5/S3/Zeros/Symmetry/CriticalDampingFlatness](../../Zeros/Symmetry/CriticalDampingFlatness.md)
