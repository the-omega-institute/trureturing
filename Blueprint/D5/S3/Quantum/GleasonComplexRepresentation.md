# Finite complex projection Gleason representation

## Abstract

Finite complex projection Gleason representation

**Theorem 1.1 (Finite complex projection Gleason representation).**

$$\forall N \in \mathit{Nat},\; \forall OP \in \operatorname{ProjectionPackage}\left(N\right),\; 3 \le N \Rightarrow \left(\exists rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), C\right),\; \left(\operatorname{PosSemidef}\left(\mathit{rho}\right) \land \left(\operatorname{trace}\left(\mathit{rho}\right) = 1 \land \left(\forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), C\right),\; \operatorname{IsStarProjection}\left(P\right) \Rightarrow \operatorname{p}\left(\mathit{OP}, P\right) = \operatorname{Re}\left(\operatorname{trace}\left(\mathit{rho} \cdot P\right)\right)\right)\right)\right) \land \left(\forall sigma \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), C\right),\; \left(\operatorname{PosSemidef}\left(\mathit{sigma}\right) \land \left(\operatorname{trace}\left(\mathit{sigma}\right) = 1 \land \left(\forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), C\right),\; \operatorname{IsStarProjection}\left(P\right) \Rightarrow \operatorname{p}\left(\mathit{OP}, P\right) = \operatorname{Re}\left(\operatorname{trace}\left(\mathit{sigma} \cdot P\right)\right)\right)\right)\right) \Rightarrow \mathit{sigma} = \mathit{rho}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GleasonComplexRepresentation.gleason_representation` (`✓ std3`). ∎

*Citation.* Andrew M. Gleason (1957). *Measures on the Closed Subspaces of a Hilbert Space*. DOI: [10.1512/iumj.1957.6.56050](https://doi.org/10.1512/iumj.1957.6.56050).

*Commentary.*

For every natural dimension N at least three and every projection package OP on complex N by N matrices, there is exactly one matrix rho that is positive semidefinite, has trace one, and satisfies OP.p(P) = Re(trace(rho P)) for every star projection P. The package is a total matrix function, constrained only by nonnegative projection values, normalization at the identity and binary additivity on orthogonal star projections.

Restrict the rank-one frame function to every completely real orthonormal triple. The real sphere theorem gives a quadratic restriction there. Extending each real orthonormal pair to such a triple gives real-plane regularity. Comparing rotated pairs shows the cross term depends linearly on the real and imaginary parts of a unit phase.

The homogeneous extension of the frame function to all vectors satisfies the parallelogram law. Integer quadratic polarization and bounded additive real linearity yield a sesquilinear form. Its standard-basis matrix is Hermitian and has the original function as its diagonal quadratic form. Mixed real scalar identities are derived in this construction, rather than assumed.

Sphere positivity gives positive semidefiniteness, and the standard orthonormal frame sum gives trace one. Spectral resolution of a star projection has eigenvalues zero or one, so finite orthogonal additivity extends the rank-one formula to every projection. Equality on all rank-one projections determines the matrix, proving uniqueness.

The notation Law(rho) in the formula abbreviates precisely positive semidefiniteness, trace one and equality on every star projection, with OP and N bound as displayed. Projective noncontextuality and the all-projections domain are mathematical premises. The theorem does not derive them empirically. It treats finite complex matrices only; the separable infinite-dimensional theorem, countable additivity, trace-class operators and an infinite-dimensional trace-one conclusion require additional results.

## References

- Truth anchor: `D5/S3/Quantum/GleasonComplexRepresentation.gleason_representation`
- Dependency: [D5/S3/QuadraticForms/ParallelogramConstruction](../QuadraticForms/ParallelogramConstruction.md)
- Dependency: [D5/S3/Quantum/GleasonFrameGeometry](GleasonFrameGeometry.md)
- Dependency: [D5/S3/Quantum/GleasonRealRepresentation](GleasonRealRepresentation.md)
