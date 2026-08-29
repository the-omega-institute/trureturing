# Archimedean Jump Decomposition

## Abstract

The completed-zeta Archimedean term is its mass contribution plus a nonnegative continuous translation energy.

**Theorem 1.1 (Archimedean jump decomposition).**

$$\forall f\in \mathcal{W}, hArch: \operatorname{ArchimedeanConvergent}(\operatorname{convolutionSquare}\left(f\right)) \Rightarrow \operatorname{archimedeanTerm}\left(\operatorname{convolutionSquare}\left(f\right), hArch\right) = \operatorname{archimedeanConstant} \cdot \operatorname{l2Mass}\left(f\right) + \operatorname{archimedeanJumpEnergy}\left(f\right) \land 0 \le \operatorname{archimedeanJumpEnergy}\left(f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition.archimedean_jump_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The test function lies in the canonical carrier of even smooth compactly supported complex-valued functions. The displayed hArch premise is the exact integrability witness consumed by archimedeanTerm.

The jump density is exp(-x/2)/(1-exp(-2x)) on positive scales, and the jump energy integrates the squared displacement of f by translation against that density. The proof derives its Levy representation from the frozen digamma series and applies Fourier inversion and Tonelli.

The first public conjunct is the exact complex identity. The second public conjunct records positivity of the independently constructed continuous jump energy.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition.archimedean_jump_decomposition`
- Dependency: [D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity](../TestFunctions/ConvolutionSquarePositivity.md)
