# Pole Rank-One Decomposition

## Abstract

The completed-zeta pole pair of a convolution square is one positive boundary observation energy.

**Theorem 1.1 (The pole pair is one boundary observation energy).**

$$\forall f\in \mathcal{W}, \operatorname{poleTerm}(\operatorname{convolutionSquare}(f)) = 2 \Vert\int_{\mathbb{R}} \exp(\frac{x}{2}) f(x) dx\Vert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PoleRankOneDecomposition.pole_rank_one_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here W is the frozen carrier of even smooth compactly supported complex functions on the real line. The convolution square and pole term are the existing canonical objects. Evenness identifies the two half-frequency boundary readings, while the frozen complex-frequency convolution factorization turns each pole evaluation into the squared modulus of the displayed integral.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/PoleRankOneDecomposition.pole_rank_one_decomposition`
- Dependency: [D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds](ConvolutionSquareOrbitBounds.md)
