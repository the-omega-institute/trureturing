# Boundary sphere coverage from directed ridges

## Abstract

Directed ridge certificates imply four-dimensional spherical cap coverage.

**Theorem 1.1 (Soundness of the directed-ridge cover checker).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/BoundarySphereCover.sphereCovered`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/BoundarySphereCover.sphereCovered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An accepted list of integer caps and simplicial facets covers every positive-radius sphere over a lawful ordered field. For a direction, maximize the dual pairing over the finite facet list. A negative basis coefficient would make the corresponding directed neighbor improve this pairing. The squared dual norm then bounds the sum of the nonnegative coefficients by one, forcing a cap inequality.

No global fan or completeness of convex-hull enumeration is a premise. A pinned atlas chart is a kernel-checked concrete application. Coverage does not imply transfer between charts or nonexistence of four mutually unbiased bases.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/BoundarySphereCover.sphereCovered`
