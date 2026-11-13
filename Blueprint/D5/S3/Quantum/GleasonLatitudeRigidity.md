# Rigidity of simple frame functions

## Abstract

Rigidity of simple frame functions

**Theorem 1.1 (Rigidity of simple frame functions).**

$$\forall f \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right) \to R,\; \forall W \in R,\; \forall p \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \forall m \in R,\; \left(\operatorname{IsFrameFunction}\left(R, f, W\right) \land \left(\operatorname{norm}\left(p\right) = 1 \land \left(\left(\forall x \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \operatorname{norm}\left(x\right) = 1 \Rightarrow f\left(x\right) \le f\left(p\right)\right) \land \left(\forall e \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \operatorname{equator}\left(p, e\right) \Rightarrow f\left(e\right) = m\right)\right)\right)\right) \Rightarrow \left(\forall s \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \operatorname{norm}\left(s\right) = 1 \Rightarrow f\left(s\right) = m + \left(f\left(p\right) - m\right) \cdot \operatorname{latitude}\left(p, s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GleasonLatitudeRigidity.eq_add_mul_latitude` (`✓ std3`). ∎

*Citation.* Andrew M. Gleason (1957). *Measures on the Closed Subspaces of a Hilbert Space*. DOI: [10.1512/iumj.1957.6.56050](https://doi.org/10.1512/iumj.1957.6.56050).

*Commentary.*

Let f be a real frame function of arbitrary weight W on all orthonormal bases of real three-space. Suppose a unit vector p is a global maximum on the sphere and f has the constant value m on the equator perpendicular to p. Then f at every unit vector s equals m plus the difference f(p) minus m times the latitude of s.

The frame identity makes equatorial points global minima. A four-point identity makes f monotone along every descent, and finite geometric descent makes it monotone in latitude. Suprema and infima along a fixed latitude can differ at only countably many latitude values.

Outside those exceptional latitudes, a one-dimensional frame sum and monotonicity determine the value. Rational multiples of one latitude are chosen to avoid the countable exceptional set; rational squeezing then fixes the linear slope. Approaching an exceptional latitude from both sides proves the same value there.

The bounded additive step uses continuity of an additive homomorphism bounded on a neighbourhood of zero, followed by real scalar linearity. Continuity is derived for that additive homomorphism; it is never imposed on f. All statements quantify over functions and real parameters rather than over a finite list of numerical examples.

## References

- Truth anchor: `D5/S3/Quantum/GleasonLatitudeRigidity.eq_add_mul_latitude`
- Dependency: [D5/S3/Quantum/GleasonFrameGeometry](GleasonFrameGeometry.md)
