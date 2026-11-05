# Mutually Unbiased Diagonal Planes

## Abstract

Mutual unbiasedness is exactly orthogonality of the traceless diagonal planes.

**Definition 1.1 (The two coordinate projectors).**

$$(\operatorname{coordinateProjectorTwo}: \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)) = ![!![1,0;0,0],!![0,0;0,1]]$$

*Formalization.* `D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.coordinateProjectorTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two complex qubit coordinate projectors select the first and second basis vectors.

**Definition 1.2 (The coordinate rank-one context).**

$$\operatorname{RankOneContext}.\operatorname{projector}\left((\operatorname{coordinateContextTwo}: \operatorname{RankOneContext}\left(2\right))\right) = \operatorname{coordinateProjectorTwo}$$

*Formalization.* `D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.coordinateContextTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The context has coordinateProjectorTwo as its projector family. Each member is Hermitian, idempotent and trace one, and compresses every matrix X to trace(PX) times P. The two members sum to the identity. These properties supply the rankOne and resolvesIdentity fields of RankOneContext; its projector family determines the context because the other fields are proofs.

**Theorem 1.3 (Mutually unbiased diagonal planes).**

$$(\operatorname{MutuallyUnbiased}(B, C) \iff \operatorname{OrthogonalTracelessPlanes}(B, C)) \land \\(\operatorname{OrthogonalTracelessPlanes}(B, C) \iff \operatorname{TraceZeroComposition}(B, C)) \land \\(\operatorname{TraceZeroComposition}(B, C) \iff \operatorname{ScalarTraceComposition}(B, C)) \land \\(\operatorname{ScalarTraceComposition}(B, C) \iff \operatorname{MutuallyUnbiased}(B, C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.mutually_unbiased_diagonal_planes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B and C be complete rank-one projective basis contexts in complex dimension d, with d at least two. Mutual unbiasedness means that every cross-context projector overlap has real trace equal to the inverse of d.

The diagonal plane of a context is constructed on the exact real trace-zero Hermitian carrier: subtract the scalar trace component from each rank-one projector and take their real span. The two planes are orthogonal exactly when all cross overlaps are uniform.

Equivalently, both orders of the unread projective measurement vanish on every trace-zero Hermitian matrix. On an arbitrary Hermitian matrix, both orders instead return its scalar trace component, namely the trace divided by d times the identity.

All four equivalences are public. The proof expands the centered Hilbert--Schmidt pairing, applies the rank-one compression law, and uses the identity resolution to evaluate both measurement compositions. Repository, pinned-library, and Loogle searches found no theorem packaging these clauses on the same carriers.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.coordinateContextTwo`
- Truth anchor: `D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.coordinateProjectorTwo`
- Truth anchor: `D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.mutually_unbiased_diagonal_planes`
- Dependency: [D5/S3/Observer/Conditioning](../../Observer/Conditioning.md)
- Dependency: [D5/S3/Quantum/Tomography/OneStepProbabilityInnovation](OneStepProbabilityInnovation.md)
