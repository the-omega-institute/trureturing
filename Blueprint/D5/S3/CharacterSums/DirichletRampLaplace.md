# Laplace transforms on the line of real part two

## Abstract

Laplace transforms of character-weighted Mangoldt ramps

For a complex Dirichlet character χ of positive modulus, the character ramp weights each von Mangoldt ramp by χ(n). The transform is taken in the coordinate y = log x over y > 0, with s(t) = 2 + 2πit for any real frequency t. Here L denotes the Dirichlet L-function and L′ its complex derivative in the first variable.

**Theorem 1.1 (The twisted transform for every character).**

$$\forall N \in \mathbb{N}, chi \in \operatorname{DirichletCharacter}\left(\mathbb{C}, N\right), t \in \mathbb{R},\; 0 < N \Rightarrow \int_{y>0} \exp\left(-s\left(t\right) y\right) \operatorname{characterRamp}\left(chi, \exp\left(y\right)\right)\,dy = \frac{-\frac{L'\left(s\left(t\right), chi\right)}{L\left(s\left(t\right), chi\right)}}{s\left(t\right)(s\left(t\right)-1)}$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletRampLaplace.characterRamp_line_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At fixed y the ramp terms are supported on positive integers at most exp y. The character norm is at most one, so the summable integrals of the unweighted ramp norms dominate the twisted ones. This gives absolute sum–integral interchange. The individual ramp transforms give the twisted von Mangoldt series divided by s(s − 1). The Dirichlet series for the negative logarithmic derivative identifies its sum.

**Theorem 1.2 (The centered transform for a nonprincipal character).**

$$\forall N \in \mathbb{N}, chi \in \operatorname{DirichletCharacter}\left(\mathbb{C}, N\right), t \in \mathbb{R},\; \left(0 < N \land chi \ne 1\right) \Rightarrow \int_{y>0} \exp\left(-s\left(t\right) y\right) \operatorname{gChi}\left(chi, \exp\left(y\right)\right)\,dy = \frac{-\frac{L'\left(s\left(t\right), chi\right)}{L\left(s\left(t\right), chi\right)}}{s\left(t\right)(s\left(t\right)-1)}+\frac{\frac{L'\left(1, chi\right)}{L\left(1, chi\right)}}{s\left(t\right)-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletRampLaplace.gChi_line_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonprincipal χ the centered ramp adds x times L′(1,χ)/L(1,χ) to the character ramp. The character ramp times the transform kernel is integrable by domination by the complete Mangoldt ramp. The added term is an integrable exponential with exponent (1 − s)y. Integrating it adds L′(1,χ)/L(1,χ) divided by s − 1.

## References

- Truth anchor: `D5/S3/CharacterSums/DirichletRampLaplace.characterRamp_line_laplace`
- Truth anchor: `D5/S3/CharacterSums/DirichletRampLaplace.gChi_line_laplace`
- Dependency: [D5/S3/CharacterSums/DirichletRampEndpoint](DirichletRampEndpoint.md)
