# Extrema without frame-function continuity

## Abstract

Extrema without frame-function continuity

**Theorem 1.1 (Extrema without frame-function continuity).**

$$\forall f \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right) \to R,\; \forall W \in R,\; \forall M \in R,\; \forall m \in R,\; \left(\operatorname{IsFrameFunction}\left(R, f, W\right) \land \left(\left(\forall u \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \operatorname{norm}\left(u\right) = 1 \Rightarrow f\left(u\right) \le M\right) \land \left(\forall u \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \operatorname{norm}\left(u\right) = 1 \Rightarrow m \le f\left(u\right)\right)\right)\right) \Rightarrow \left(\exists p \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \operatorname{norm}\left(p\right) = 1 \land \left(\forall u \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \operatorname{norm}\left(u\right) = 1 \Rightarrow f\left(u\right) \le f\left(p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GleasonExtremum.exists_forall_le` (`✓ std3`). ∎

*Citation.* Andrew M. Gleason (1957). *Measures on the Closed Subspaces of a Hilbert Space*. DOI: [10.1512/iumj.1957.6.56050](https://doi.org/10.1512/iumj.1957.6.56050).

*Commentary.*

A frame function of arbitrary real weight, bounded above by M and below by m on the unit sphere, attains its maximum at a unit vector p. Applying this statement to the negative function also gives a minimum. Neither extremum statement assumes continuity or measurability of the frame function.

A maximizing sequence has a limiting pole on the compact sphere. This fact alone cannot pass the function values to the pole. Moving orthogonal frames and symmetrization instead create a family of bounded frame functions. A cluster point in the product of closed bounded intervals retains every frame equation because each equation is closed in finitely many coordinates.

The latitude rigidity result applies to the limiting symmetrized function. If the value at the limiting pole were strictly below the supremum, a chosen positive gap and two descent steps would contradict the inequalities along the moving frames. This proves attainment without an illicit continuity argument.

The minimum is used to select an axis orthogonal to a maximizing direction in the real quadratic representation. Extremum attainment also applies to the residual frame function after subtracting a diagonal quadratic candidate.

## References

- Truth anchor: `D5/S3/Quantum/GleasonExtremum.exists_forall_le`
- Dependency: [D5/S3/Quantum/GleasonLatitudeRigidity](GleasonLatitudeRigidity.md)
