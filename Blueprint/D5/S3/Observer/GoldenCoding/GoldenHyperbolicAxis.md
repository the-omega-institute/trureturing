# Golden Hyperbolic Axis and Observer Index

## Abstract

The golden Mobius map has two fixed endpoints and an explicit hyperbolic axis length.

**Theorem 1.1 (The golden map determines its axis and observer scale).**

$$let \operatorname{g}\left(z\right) = 1 + \frac{1}{z}; let F = \operatorname{matrix2}\left(1, 1, 1, 0\right); let \operatorname{C}\left(x, y\right) = \left(x - \frac{1}{2}\right)^{2} + y^{2} = \frac{5}{4}; \left(\left(\left(\left(\left(\left(\left(\operatorname{Fix}\left(g\right) = \left\{\varphi, \varphi'\right\} \land \left(\forall z \in \mathbb{R},\; \left(\operatorname{g}\left(z\right) = z \Leftrightarrow z^{2} = z + 1\right) \land \left(z^{2} = z + 1 \Leftrightarrow \left(z = \varphi \lor z = \varphi'\right)\right)\right)\right) \land \left(\left(\left(\varphi' = 1 - \varphi \land \varphi' = -\varphi^{-1}\right) \land \varphi \ne 0\right) \land \varphi' \ne 0\right)\right) \land \left(\forall z \in \mathbb{R},\; \left(z \ne 0 \land z \ne -1\right) \Rightarrow \operatorname{g}\left(\operatorname{g}\left(z\right)\right) = \frac{2 \cdot z + 1}{z + 1}\right)\right) \land \left(\left(\left(\operatorname{det}\left(F\right) = -1 \land F^{2} = \operatorname{matrix2}\left(2, 1, 1, 1\right)\right) \land \operatorname{det}\left(F^{2}\right) = 1\right) \land \operatorname{trace}\left(F^{2}\right) = 3\right)\right) \land \left(\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \operatorname{C}\left(x, y\right) \Leftrightarrow \left(x - \frac{1}{2}\right)^{2} + y^{2} = \frac{5}{4}\right)\right) \land \left(\left(\left(\operatorname{C}\left(\varphi, 0\right) \land \operatorname{C}\left(\varphi', 0\right)\right) \land \operatorname{C}\left(\frac{1}{2}, \frac{\operatorname{sqrt}\left(5\right)}{2}\right)\right) \land 0 < \frac{\operatorname{sqrt}\left(5\right)}{2}\right)\right) \land \left(\left(\left(\ell = 2 \cdot \operatorname{arcosh}\left(\frac{3}{2}\right) \land \ell = 4 \cdot \operatorname{log}\left(\varphi\right)\right) \land \frac{\ell}{2} = \operatorname{log}\left(\varphi^{2}\right)\right) \land \operatorname{exp}\left(-\frac{\ell}{2}\right) = \varphi^{-2}\right)\right) \land \left(\left(observerIndex = \varphi^{2} \land projectionWeight = \varphi^{-2}\right) \land \operatorname{abs}\left(goldenProjectiveMultiplier\right) = \varphi^{-2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenHyperbolicAxis.golden_hyperbolic_axis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For g(z)=1+1/z, the fixed-point equation is the golden quadratic. The two real solutions are the golden ratio and its negative conjugate, and both are nonzero genuine fixed points.

The Fibonacci matrix has determinant minus one, while its square has determinant one and trace three. The endpoint circle in the upper half-plane is centered at one half with squared radius five fourths.

The trace formula reduces the translation length to four log phi. Its half-length is the logarithm of the observer index phi squared, and the decaying projective weight is phi to the minus two.

No projective-line action structure, hyperbolic-isometry classification, Jones projection, six-dimensional lattice, or Riemann-scattering claim is introduced, because the source does not supply formal definitions from which those narrative identifications follow.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenHyperbolicAxis.golden_hyperbolic_axis`
- Dependency: [D5/S0/Tower/QuadraticFixedPoint](../../../S0/Tower/QuadraticFixedPoint.md)
- Dependency: [D5/S1/Eigenstructure/FibonacciMatrixDiscriminant](../../../S1/Eigenstructure/FibonacciMatrixDiscriminant.md)
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix](../../CompletionDynamics/GoldenMobius/GoldenScaleHelix.md)
