# Mutually Unbiased Diagonal Planes

## Abstract

Mutual unbiasedness is exactly orthogonality of the traceless diagonal planes.

**Theorem 1.1 (Mutually unbiased diagonal planes).**

$$(\operatorname{MutuallyUnbiased}(B, C) \iff \operatorname{OrthogonalTracelessPlanes}(B, C)) \land \\(\operatorname{OrthogonalTracelessPlanes}(B, C) \iff \operatorname{TraceZeroComposition}(B, C)) \land \\(\operatorname{TraceZeroComposition}(B, C) \iff \operatorname{ScalarTraceComposition}(B, C)) \land \\(\operatorname{ScalarTraceComposition}(B, C) \iff \operatorname{MutuallyUnbiased}(B, C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.mutually_unbiased_diagonal_planes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B and C be complete rank-one projective basis contexts in complex dimension d, with d at least two. Mutual unbiasedness means that every cross-context projector overlap has real trace equal to the inverse of d.

The diagonal plane of a context is constructed on the exact real trace-zero Hermitian carrier: subtract the scalar trace component from each rank-one projector and take their real span. The two planes are orthogonal exactly when all cross overlaps are uniform.

Equivalently, both orders of the unread projective measurement vanish on every trace-zero Hermitian matrix. On an arbitrary Hermitian matrix, both orders instead return its scalar trace component, namely the trace divided by d times the identity.

All four equivalences are public. The proof expands the centered Hilbert--Schmidt pairing, applies the rank-one compression law, and uses the identity resolution to evaluate both measurement compositions. Repository, pinned-library, and Loogle searches found no theorem packaging these clauses on the same carriers.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.mutually_unbiased_diagonal_planes`
- Dependency: [D5/S3/Observer/Conditioning](../../Observer/Conditioning.md)
- Dependency: [D5/S3/Quantum/Tomography/OneStepProbabilityInnovation](OneStepProbabilityInnovation.md)
