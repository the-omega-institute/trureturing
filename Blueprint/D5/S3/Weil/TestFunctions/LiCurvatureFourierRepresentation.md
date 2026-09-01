# Li Curvature Fourier Representation

## Abstract

Normalized Li curvature is the Fourier sequence of its symmetric Cayley probability measure.

**Theorem 1.1 (Li curvature as a probability-measure Fourier sequence).**

$$\begin{gathered}\forall rho: \operatorname{Measure}\left(\mathbb{R}\right),\\{}[\operatorname{IsProbabilityMeasure}\left(rho\right)] \Rightarrow\\{}\operatorname{let} phase: \mathbb{R} \to Circle := xi: \mathbb{R} \mapsto \operatorname{cayleyCircle}\left(\frac{1}{2}, xi\right),\\{}\operatorname{let} reflectedPhase: \mathbb{R} \to Circle := xi: \mathbb{R} \mapsto \operatorname{pow}\left(phase\left(xi\right), {-1}\right),\\{}\operatorname{let} liEnergy: \mathbb{Z} \to \mathbb{R} \to \mathbb{R} := n: \mathbb{Z} \mapsto xi: \mathbb{R} \mapsto \frac{4 \cdot xi^{2} + 1}{2} \cdot (1 - \operatorname{Re}\left(\operatorname{pow}\left(phase\left(xi\right), n\right)\right)),\\{}\operatorname{let} normalizedLi: \mathbb{Z} \to \mathbb{R} := n: \mathbb{Z} \mapsto \operatorname{integral}\left(rho, xi: \mathbb{R} \mapsto liEnergy\left(n, xi\right)\right),\\{}\operatorname{let} liCurvature: \mathbb{Z} \to \mathbb{R} := n: \mathbb{Z} \mapsto \frac{normalizedLi\left(n + 1\right) - 2 \cdot normalizedLi\left(n\right) + normalizedLi\left(n - 1\right)}{2},\\{}\operatorname{let} curvatureMeasure: \operatorname{Measure}\left(Circle\right) := \frac{1}{2} \cdot \operatorname{map}\left(phase, rho\right) + \frac{1}{2} \cdot \operatorname{map}\left(reflectedPhase, rho\right),\\{}\operatorname{IsProbabilityMeasure}\left(curvatureMeasure\right) \land\\{}(\forall n: \mathbb{Z}, \operatorname{complexCast}\left(liCurvature\left(n\right)\right) = \operatorname{integral}\left(curvatureMeasure, z: Circle \mapsto z^{n}\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LiCurvatureFourierRepresentation.li_curvature_fourier_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normalized distribution of positive ordinates determines the half-scale Cayley phase and its reflection. Their equally weighted pushforwards construct the symmetric circle measure.

The Li energy is constructed from the reciprocal Cayley weight and the real part of each integral phase power. Its normalized second difference is the corresponding circle moment.

The Cayley power estimate makes every energy kernel bounded, so the second difference passes through the source integral without an extra moment premise. The symmetric measure has total mass one and supplies every integer Fourier coefficient.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/LiCurvatureFourierRepresentation.li_curvature_fourier_representation`
- Dependency: [D5/S3/Weil/TestFunctions/CayleyMomentTransport](CayleyMomentTransport.md)
