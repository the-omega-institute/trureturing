# Rational-Toeplitz Collapse

## Abstract

A common denominator converts a rational feature Gram matrix into a congruence of one weighted monomial moment matrix.

**Theorem 1.1 (A common denominator gives one moment congruence).**

$$\begin{aligned}\forall n: \mathbb{N}, mu: \operatorname{FiniteMeasure}(Circle),\\A: \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \mathbb{C}), D: \operatorname{Polynomial}(\mathbb{C}),\\hD: \forall z \in Circle,\; \operatorname{eval}(D, z) \neq 0,\\\operatorname{let}(v: Circle \to \left(\operatorname{Fin}(n) \to \mathbb{C}\right), \forall z: Circle, j: \operatorname{Fin}(n), v(z)(j) = z^{j}\;\psi: Circle \to \left(\operatorname{Fin}(n) \to \mathbb{C}\right), \forall z: Circle, i: \operatorname{Fin}(n), \psi(z)(i) = \frac{\operatorname{mulVec}(A, v(z))(i)}{\operatorname{eval}(D, z)}\;\Sigma: \operatorname{Measure}(Circle) = \operatorname{withDensity}(mu, (z: Circle \mapsto \operatorname{ofReal}(\operatorname{normSq}(\operatorname{eval}(D, z))^{-1})))\;G: \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \mathbb{C}), \forall i: \operatorname{Fin}(n), j: \operatorname{Fin}(n), G_{i,j} = \operatorname{integral}(mu, (z: Circle \mapsto \psi(z)(i) \cdot {\psi(z)(j)}^{*}))\;T: \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \mathbb{C}), \forall i: \operatorname{Fin}(n), j: \operatorname{Fin}(n), T_{i,j} = \operatorname{integral}(\Sigma, (z: Circle \mapsto v(z)(i) \cdot {v(z)(j)}^{*}))),\\G = A \cdot T \cdot \operatorname{conjTranspose}(A).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/RationalToeplitzCollapse.rational_toeplitz_collapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite positive measure on the unit circle, a complex coefficient matrix, and a polynomial without unit-circle zeros construct the monomial and rational feature vectors.

The weighted measure uses the reciprocal norm-square of the supplied denominator. Compactness of the circle and nonvanishing of the denominator make this measure finite.

Expanding both finite matrix products and moving their scalar coefficients through the integral identifies the rational Gram matrix with the displayed congruence.

## References

- Truth anchor: `D5/S3/Observer/BlockStructure/RationalToeplitzCollapse.rational_toeplitz_collapse`
