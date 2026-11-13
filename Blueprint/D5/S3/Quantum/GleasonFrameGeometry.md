# Finite descent on the real sphere

## Abstract

Finite descent on the real sphere

**Theorem 1.1 (Finite descent on the real sphere).**

$$\forall p \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \forall s \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \forall t \in \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; \left(\operatorname{norm}\left(p\right) = 1 \land \left(\operatorname{northern}\left(p, s\right) \land \left(\left(\neg s = p\right) \land \left(\operatorname{northern}\left(p, t\right) \land \left(\left(\neg t = p\right) \land \operatorname{latitude}\left(p, t\right) < \operatorname{latitude}\left(p, s\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists n \in \mathit{Nat},\; \exists c \in \mathit{Nat} \to \operatorname{EuclideanSpace}\left(R, \operatorname{Fin}\left(3\right)\right),\; 1 \le n \land \operatorname{IsDescentChain}\left(p, s, t, n, c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GleasonFrameGeometry.exists_descent_chain` (`✓ std3`). ∎

*Citation.* Andrew M. Gleason (1957). *Measures on the Closed Subspaces of a Hilbert Space*. DOI: [10.1512/iumj.1957.6.56050](https://doi.org/10.1512/iumj.1957.6.56050).

*Commentary.*

The adopted elementary real core (Sphere through General) follows Cooke, Keane, Moran (1985), Math. Proc. Cambridge Philos. Soc. 98, 117–128.

The ambient space is real Euclidean three-space. A unit pole p determines its northern closed hemisphere, the unit vectors s with nonnegative inner product with p. Latitude is the square of that inner product. A descent step stays on the great circle orthogonal to the coldest equatorial direction associated with its starting point.

For two northern unit vectors distinct from the pole, strictly decreasing latitude is realized by a finite descent chain. IsDescentChain records both endpoints, membership of every indexed vector in the northern hemisphere away from the pole, and the descent relation at every successive index. The natural number n is at least one.

The construction lifts tangent coordinates to the sphere. A complex spiral rotates the tangent direction while increasing its radius; a cosine estimate selects a finite number of steps. Two additional ray steps correct the endpoint. No property or continuity of a frame function enters this geometric construction.

A projection package is a total real-valued function on complex square matrices. Only star projections are constrained: nonnegative values, value one at the identity and binary additivity when the projection product is zero. Rank-one projection values therefore sum to one on every orthonormal basis. The associated real frame identity is a sum of three values on each orthonormal triple.

## References

- Truth anchor: `D5/S3/Quantum/GleasonFrameGeometry.exists_descent_chain`
