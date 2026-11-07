# Finite power radial kernel

## Abstract

The exact radial Hessian kernel of the actual finite power trace on every coupled rank two support face.

**Theorem 1.1 (Exact radial kernel on each coupled rank two face).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerKernel.radial_hessian_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerKernel.radial_hessian_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite column type and every real 1 < q < 2, let W be a nonnegative two row table with positive definite row Gram and at least one overlapping column. If V vanishes at each zero coordinate of W, then the actual second derivative at zero of t -> Fq q (W + t V) vanishes if and only if V is a real scalar multiple of W. No derivative or Hessian sign is assumed. The proof reuses the full three coordinate inverse metric from the concavity supplier, deletes zero columns by an exact Gram equality, and retains every axial nonzero column through its restricted support metric. The velocity is normalized by z = dotW/(q*x^(2q-1)), so dotx = z/2; the conversion back to the actual table derivative includes the resulting factor q. Purely axial tables and rank one Grams are outside this radial assertion. The theorem does not assert a universal equality classification on those excluded cases or solve the original arbitrary complex Audenaert problem.

## References

- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerKernel.radial_hessian_kernel`
- Dependency: [D5/S3/Quantum/NormCompression/FinitePowerConcavity](FinitePowerConcavity.md)
