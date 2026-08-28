# The Sixfold Golden Heat Midline

## Abstract

The golden heat spectrum has a single exact line selected by reflection, half-density unitarity, square summability, and self-resonance.

**Theorem 1.1 (The golden heat spectrum has the sixfold midline).**

$$\begin{gathered}(\forall s\in\mathbb{C}, s=\frac{1}{\varphi^{2}}-\overline{s} \Leftrightarrow \Re(s)=\frac{1}{2\varphi^{2}}) \land\\{}(\forall s\in\mathbb{C}, (\forall a, |\operatorname{halfDensityCoefficient}(\operatorname{goldenSpectrum},\frac{1}{\varphi^{2}},s,a)|=1) \Leftrightarrow \Re(s)=\frac{1}{2\varphi^{2}}) \land\\{}(\forall \sigma,t\in\mathbb{R}, \frac{1}{2\varphi^{2}}<\sigma \Rightarrow \operatorname{let} \mathbf{Z}_{gold} := \operatorname{heatCoefficient}(\operatorname{goldenSpectrum}, \sigma+it); \left\Vert\mathbf{Z}_{gold}\right\Vert^{2}=\operatorname{heatTrace}(\operatorname{goldenSpectrum},2\sigma)) \land\\{}(\forall s\in\mathbb{C}, \operatorname{MemLp}(\operatorname{heatCoefficient}(\operatorname{goldenSpectrum},s),2) \Leftrightarrow \frac{1}{2\varphi^{2}}<\Re(s)) \land\\{}(\forall s\in\mathbb{C}, \operatorname{KernelResonant}(\frac{1}{\varphi^{2}},s,s) \Leftrightarrow \Re(s)=\frac{1}{2\varphi^{2}}) \land\\{}(\forall s,w\in\mathbb{C}, \operatorname{KernelResonant}(\frac{1}{\varphi^{2}},s,w) \Leftrightarrow w=\frac{1}{\varphi^{2}}-\overline{s}). \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/HeatLayers/GoldenHeatMidline.golden_heat_sixfold_midline` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugate reflection and coordinatewise unit modulus after the canonical half-density normalization select real part one over twice phi squared. The labeled coefficient vector is constructed directly from the frozen golden spectrum and its exact square-summability proof; its squared norm is the heat trace at twice the real parameter and is independent of the vertical coordinate.

Boundary divergence of the ground prime layer supplies the strict L2 iff. The resonance equation selects the same self-line and identifies every parameter's unique partner as one over phi squared minus its conjugate.

The numerical window checks attached to the source are empirical evidence outside the named theorem and are not encoded as deductive clauses.

## References

- Truth anchor: `D5/S3/Midline/HeatLayers/GoldenHeatMidline.golden_heat_sixfold_midline`
- Dependency: [D5/S3/Midline/UniversalHeatTrace](../UniversalHeatTrace.md)
