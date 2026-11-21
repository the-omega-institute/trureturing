# The Klein model on the open Bloch ball

## Abstract

The open Bloch ball with the Klein distance is isometric to hyperbolic three-space, and the filters of invertible two-by-two complex matrices act on it by isometries, transitively already through positive definite matrices of determinant one.

**Definition 1.1 (The Klein distance function).**

$$\forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), s \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{kleinCosh}\left(r, s\right) = \frac{1 - \langle r, s \rangle}{\sqrt{\left(1 - \left\lVert r \right\rVert^{2}\right) \cdot \left(1 - \left\lVert s \right\rVert^{2}\right)}}$$

*Formalization.* `D5/S3/Geometry/BlochBallKleinModel.kleinCosh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For vectors r and s of the Euclidean space R^3, kleinCosh(r, s) = (1 - <r, s>) / sqrt((1 - |r|^2) (1 - |s|^2)). On the open unit ball this is the hyperbolic cosine of the hyperbolic distance in the Beltrami-Klein model. The formula has this meaning only for |r| < 1 and |s| < 1. Elsewhere it is still defined: the product (1 - |r|^2) (1 - |s|^2) is zero when a point lies on the unit sphere, negative when one point lies inside the unit sphere and the other outside, and positive when both lie outside. In the first two cases the square root is 0 (by convention for a negative argument) and division by 0 gives 0, so kleinCosh is 0; in the last case the quotient is a real number without hyperbolic meaning.

**Definition 1.2 (The filter of a matrix on Bloch vectors).**

$$\forall g \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{filter}\left(g, r\right) = \operatorname{re}\left(\operatorname{trace}\left(g \cdot \operatorname{blochMatrix}\left(1, r\right) \cdot \operatorname{conjTranspose}\left(g\right)\right)\right)^{-1} \cdot \operatorname{bloch}\left(g \cdot \operatorname{blochMatrix}\left(1, r\right) \cdot \operatorname{conjTranspose}\left(g\right)\right)$$

*Formalization.* `D5/S3/Geometry/BlochBallKleinModel.filter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a two-by-two complex matrix g and a vector r of R^3, let rho(r) = blochMatrix(1, r) = (1 + r_x X + r_y Y + r_z Z) / 2 be the Hermitian matrix of trace one with Bloch vector r, where X, Y, Z are the Pauli matrices. The filter sends r to the Bloch vector of the normalized matrix g rho(r) g^H / Re tr(g rho(r) g^H): with M = g rho(r) g^H, filter(g, r) is the scalar (Re tr M)^(-1) times bloch(M), the vector of Pauli coefficients of M. In the display g^H is written conjTranspose(g) and the scalar action is written as a product. On density matrices this is the map rho -> g rho g^H / tr(g rho g^H).

**Theorem 1.3 (The open Bloch ball is hyperbolic three-space).**

$$\left(\exists Phi \in \operatorname{Equiv}\left(\{v \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right) \mid \left\lVert v \right\rVert < 1\}, \operatorname{HyperbolicThreeSpace}\right),\; \forall r \in \{v \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right) \mid \left\lVert v \right\rVert < 1\}, s \in \{v \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right) \mid \left\lVert v \right\rVert < 1\},\; \operatorname{cosh}\left(\operatorname{dist}\left(Phi\left(r\right), Phi\left(s\right)\right)\right) = \operatorname{kleinCosh}\left(r, s\right)\right) \land \left(\left(\forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{filter}\left(1, r\right) = r\right) \land \left(\left(\forall g \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{det}\left(g\right) \ne 0 \Rightarrow \left(\left(\forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \left\lVert r \right\rVert < 1 \Rightarrow \left\lVert \operatorname{filter}\left(g, r\right) \right\rVert < 1\right) \land \left(\left(\forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \left\lVert r \right\rVert \le 1 \Rightarrow \left(\forall h \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{filter}\left(h, \operatorname{filter}\left(g, r\right)\right) = \operatorname{filter}\left(h \cdot g, r\right)\right)\right) \land \left(\forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), s \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \left\lVert r \right\rVert < 1 \Rightarrow \left(\left\lVert s \right\rVert < 1 \Rightarrow \operatorname{kleinCosh}\left(\operatorname{filter}\left(g, r\right), \operatorname{filter}\left(g, s\right)\right) = \operatorname{kleinCosh}\left(r, s\right)\right)\right)\right)\right)\right) \land \left(\forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \left\lVert r \right\rVert < 1 \Rightarrow \left(\exists g \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{PosDef}\left(g\right) \land \left(\operatorname{det}\left(g\right) = 1 \land \operatorname{filter}\left(g, 0\right) = r\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/BlochBallKleinModel.bloch_ball_hyperbolic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James W. Cannon, William J. Floyd, Richard Kenyon, and Walter R. Parry (1997). *Hyperbolic Geometry*. URL: <https://library.slmath.org/books/Book31/files/cannon.pdf>.

*Commentary.*

The statement has four clauses. (1) There is a bijection Phi from the open ball {v in R^3 | |v| < 1} onto HyperbolicThreeSpace, the upper half-space model of hyperbolic three-space with its hyperbolic metric, such that cosh(dist(Phi(r), Phi(s))) = kleinCosh(r, s) for all r and s in the open ball. (2) The filter of the identity matrix is the identity: filter(1, r) = r for every r. (3) For every complex matrix g with det(g) nonzero: for every r with |r| < 1 the filtered vector filter(g, r) again has norm less than 1; for every r with |r| <= 1, that is on the closed ball, filter(h, filter(g, r)) = filter(h g, r) for every matrix h; and filter(g, .) preserves kleinCosh on the open ball, so it acts as an isometry of the Klein distance. (4) For every r with |r| < 1 there is a positive definite matrix g of determinant 1 with filter(g, 0) = r.

Clause (1) uses the Klein chart r -> (r, 1) / sqrt(1 - |r|^2), a bijection of the open ball onto the future sheet of the unit hyperboloid of the Lorentz form with space-positive and time-negative signature; the Lorentz product of the images of r and s is -(1 - <r, s>) / sqrt((1 - |r|^2) (1 - |s|^2)), and the identity a * b = -cosh(d(a, b)) for points of the future sheet, together with the identification of that sheet with the upper half-space, gives the formula; the inverse map takes the spatial part of a hyperboloid point divided by its time part. Clause (3): for two-by-two matrices, the polarized determinant tr(X adj(Y)) satisfies tr(g X g^H adj(g Y g^H)) = |det g|^2 tr(X adj(Y)), and 1 - <r, s> = 2 tr(rho(r) adj(rho(s))); the positive normalizing factors and |det g|^2 cancel in kleinCosh, which is homogeneous of degree zero. Positive definiteness of rho(r) for |r| < 1 is preserved by g rho(r) g^H when det(g) is nonzero, and det rho(r) = (1 - |r|^2) / 4 is then positive, so the filtered vector stays in the open ball. For the composition law on the closed ball, rho(r) is positive semidefinite and of trace one when |r| <= 1, so g rho(r) g^H is positive semidefinite and nonzero for invertible g, and its trace is a positive real number; the scalar factor (Re tr M)^(-1) is therefore nonzero and cancels in the normalization. Clause (4): g is a positive multiple of a square root of rho(r), normalized to determinant one.

The hypothesis det(g) nonzero is needed; this example is not formalized: for the singular matrix g = diag(1, 0) the matrix g rho(r) g^H is a multiple of diag(1, 0) for every r, so every point of the open ball is sent to the north pole (0, 0, 1), which has norm 1. The Klein and hyperboloid models of hyperbolic space and the action of SL(2, C) on Hermitian matrices by X -> g X g^H, which is the spinor map onto the identity component of the Lorentz group, are classical; the statement here takes all invertible complex matrices, the scalar factor cancelling in the normalization. The four clauses state neither that filters give every orientation-preserving isometry nor how two filters compose into a boost followed by a rotation.

## References

- Truth anchor: `D5/S3/Geometry/BlochBallKleinModel.bloch_ball_hyperbolic`
- Truth anchor: `D5/S3/Geometry/BlochBallKleinModel.filter`
- Truth anchor: `D5/S3/Geometry/BlochBallKleinModel.kleinCosh`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramMetricSegments](Hyperideal/LengthGramMetricSegments.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Quantum/Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Information/ActualQubitChordObstruction](../Quantum/Information/ActualQubitChordObstruction.md)
