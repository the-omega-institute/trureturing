# Radial Boundary Phase Derivative

## Abstract

The normal logarithmic Cayley radius and its smooth boundary phase have the same Poisson-kernel derivative.

**Theorem 1.1 (Radial and boundary phase derivatives coincide).**

$$\begin{gathered}\forall a, gamma: \operatorname{Real}\left(\right),\\{}0 < a \Rightarrow\\{}\operatorname{let} cayleyCoordinate: \operatorname{Real}\left(\right) \to \left(\operatorname{Real}\left(\right) \to \operatorname{Complex}\left(\right)\right) := (gamma: \operatorname{Real}\left(\right), delta: \operatorname{Real}\left(\right) \mapsto \frac{\operatorname{complex}\left(gamma\right) - Complex.I \cdot \operatorname{complex}\left(delta\right) + Complex.I \cdot \operatorname{complex}\left(a\right)}{\operatorname{complex}\left(gamma\right) - Complex.I \cdot \operatorname{complex}\left(delta\right) - Complex.I \cdot \operatorname{complex}\left(a\right)}),\\{}\operatorname{let} radialCoordinate: \operatorname{Real}\left(\right) \to \left(\operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right)\right) := (gamma: \operatorname{Real}\left(\right), delta: \operatorname{Real}\left(\right) \mapsto \operatorname{log}\left(\left\lVert cayleyCoordinate\left(gamma, delta\right) \right\rVert\right)),\\{}\operatorname{let} boundaryPhase: \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right) := (gamma: \operatorname{Real}\left(\right) \mapsto Real.pi - 2 \cdot \operatorname{arctan}\left(\frac{gamma}{a}\right)),\\{}\operatorname{let} poissonKernel: \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right) := (gamma: \operatorname{Real}\left(\right) \mapsto \operatorname{RiemannPoissonDensityPoissonKernel}\left(a, gamma\right)),\\{}\operatorname{complex}\left(Circle.exp\left(boundaryPhase\left(gamma\right)\right)\right) = cayleyCoordinate\left(gamma, 0\right) \land \left(\left\lVert cayleyCoordinate\left(gamma, 0\right) \right\rVert = 1 \land \left(\left(\forall delta \in \operatorname{Real}\left(\right),\; delta \ne 0 \Rightarrow \left\lVert cayleyCoordinate\left(gamma, delta\right) \right\rVert \ne 1\right) \land \left(\operatorname{HasDerivAt}\left((delta: \operatorname{Real}\left(\right) \mapsto radialCoordinate\left(gamma, delta\right)), -2 \cdot Real.pi \cdot poissonKernel\left(gamma\right), 0\right) \land \operatorname{HasDerivAt}\left(boundaryPhase, -2 \cdot Real.pi \cdot poissonKernel\left(gamma\right), gamma\right)\right)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/Cayley/RadialBoundaryPhaseDerivative.radial_boundary_phase_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive scale, the off-axis Cayley coordinate is constructed from the real tangential and normal coordinates. Its logarithmic norm is the radial coordinate, while pi minus twice the arctangent is a smooth real phase lift of the boundary value.

The exponential clause ties that lift to the canonical boundary Cayley point, including the branch-cut point. The norm clauses state that the coordinate is unitary exactly when the normal displacement vanishes.

Both derivative clauses use the same explicitly constructed Poisson kernel value. Thus the normal derivative of the logarithmic radius is the tangential derivative of the boundary phase.

## References

- Truth anchor: `D5/S3/Midline/Cayley/RadialBoundaryPhaseDerivative.radial_boundary_phase_derivative`
- Dependency: [D5/S3/Weil/TestFunctions/CayleyMomentTransport](../../Weil/TestFunctions/CayleyMomentTransport.md)
- Dependency: [D5/S3/Weil/ZetaAnalytic/RiemannPoissonDensity](../../Weil/ZetaAnalytic/RiemannPoissonDensity.md)
