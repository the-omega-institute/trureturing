# Perfect Projection Does Not Imply Dynamical Closure

## Abstract

A concrete perfect coordinate projection has a range that a linear dynamics fails to preserve.

**Lemma 1.1 (The first-coordinate projection is perfect).**

$$\operatorname{IsPerfectProjection}\left(firstCoordinateProjection\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/ProjectionDoesNotImplyClosure.firstCoordinateProjection_isPerfect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal rational matrix with entries one and zero projects onto the first coordinate of the two-dimensional space. Multiplying this matrix by itself leaves it unchanged, so the projection is idempotent.

The same matrix is equal to its conjugate transpose because it is real and diagonal. Idempotence together with this Hermitian symmetry makes it a perfect projection in the module's terminology.

**Theorem 1.2 (A perfect projection need not have an invariant range).**

$$\exists D, F: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{Q}\right), \operatorname{IsPerfectProjection}\left(D\right) \land \neg \operatorname{IsInvariant}\left(\operatorname{matrixToLinear}\left(F\right), \operatorname{range}\left(\operatorname{matrixToLinear}\left(D\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/ProjectionDoesNotImplyClosure.perfect_projection_does_not_imply_dynamical_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are two-by-two rational matrices D and F for which D is a perfect projection but the range of D is not invariant under the linear dynamics induced by F. Thus projection perfection alone supplies no dynamical closure guarantee.

The witnesses are the projection onto the first coordinate and the map sending the first basis vector to the second. The first basis vector lies in the projection range, while its image under the dynamics has a nonzero second coordinate and therefore lies outside that range.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/ProjectionDoesNotImplyClosure.firstCoordinateProjection_isPerfect`
- Truth anchor: `D5/S3/Observer/HiddenFlow/ProjectionDoesNotImplyClosure.perfect_projection_does_not_imply_dynamical_closure`
- Dependency: [D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity](ProjectionCommutatorIdentity.md)
