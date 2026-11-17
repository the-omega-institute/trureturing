# Quadratic representation on the real sphere

## Abstract

Quadratic representation on the real sphere

**Theorem 1.1 (Quadratic representation on the real sphere).**

$$\forall f \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right) \to R,\; \forall W \in R,\; \left(\operatorname{IsFrameFunction}\left(R, f, W\right) \land \left(\forall x \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \operatorname{norm}\left(x\right) = 1 \Rightarrow 0 \le f\left(x\right)\right)\right) \Rightarrow \left(\exists A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), R\right),\; \operatorname{IsSymm}\left(A\right) \land \left(\forall x \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \operatorname{norm}\left(x\right) = 1 \Rightarrow f\left(x\right) = \operatorname{dot}\left(x, \operatorname{mulVec}\left(A, x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GleasonRealRepresentation.frameFunction_regular_sphere` (`✓ std3`). ∎

*Citation.* Andrew M. Gleason (1957). *Measures on the Closed Subspaces of a Hilbert Space*. DOI: [10.1512/iumj.1957.6.56050](https://doi.org/10.1512/iumj.1957.6.56050).

*Commentary.*

The adopted elementary real core (Sphere through General) follows Cooke, Keane, Moran (1985), Math. Proc. Cambridge Philos. Soc. 98, 117–128. The axis choice p, r, q, target form and identities follow section 7; the original formalization uses a different endgame from the paper.

Every real-valued function whose sum is W on every orthonormal basis of real three-space, and whose values are nonnegative on the entire unit sphere, is a symmetric quadratic form on that sphere. The weight W is arbitrary; the function outside the sphere is unrestricted. No continuity or measurability hypothesis occurs.

Nonnegativity and the frame sum give upper bound W. Extremum attainment chooses a maximum p. Applying the minimum theorem to the sum of f and the squared inner product with p gives a minimizing direction r orthogonal to p. The cross product supplies the remaining orthogonal axis q.

The diagonal quadratic candidate takes the values f(p), f(q) and f(r) on those axes. The difference between this candidate and f is again a frame function. Pole rotations make its values antisymmetric and force it to vanish on four great circles.

The residual attains a maximum. The geometric half-inner-product identities and the four vanishing circles force that maximum to be zero, hence the residual vanishes everywhere on the sphere. Expanding the diagonal expression in the chosen orthonormal frame gives the symmetric real matrix.

## References

- Truth anchor: `D5/S3/Quantum/GleasonRealRepresentation.frameFunction_regular_sphere`
- Dependency: [D5/S3/Quantum/GleasonExtremum](GleasonExtremum.md)
