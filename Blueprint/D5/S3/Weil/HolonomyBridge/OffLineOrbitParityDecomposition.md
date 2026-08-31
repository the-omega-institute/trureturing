# Off-Line Orbit Parity Decomposition

## Abstract

Off-line zero orbits split into even energy minus odd energy.

**Theorem 1.1 (Off-line orbit parity decomposition).**

$$\forall Z: ZeroData, g: WeilTestFunction, n: \mathbb{N},\\{}(\operatorname{conjugation}\left(Z, n\right) \neq n) \land (\Re (\operatorname{zero}\left(Z, n\right)) \neq criticalAbscissa) \Rightarrow\\{}\operatorname{let} first: \mathbb{C} = \operatorname{fourierLaplace}\left(g, \operatorname{gamma}\left(Z, n\right)\right);\\{}\operatorname{let} second: \mathbb{C} = \operatorname{fourierLaplace}\left(g, \overline{\operatorname{gamma}\left(Z, n\right)}\right);\\{}\operatorname{let} orbitValue: \mathbb{R} = \sum_{k \in \left\{n, \operatorname{reflection}\left(Z, n\right), \operatorname{conjugation}\left(Z, n\right), \operatorname{conjugation}\left(Z, \operatorname{reflection}\left(Z, n\right)\right)\right\}} \Re (\operatorname{zeroSummand}\left(Z, \operatorname{convolutionSquare}\left(g\right), k\right));\\{}((orbitValue = \operatorname{orbitEvenEnergy}\left(\operatorname{multiplicity}\left(Z, n\right), first, second\right) - \operatorname{orbitOddEnergy}\left(\operatorname{multiplicity}\left(Z, n\right), first, second\right)) \land\\{}(0 \leq \operatorname{orbitOddEnergy}\left(\operatorname{multiplicity}\left(Z, n\right), first, second\right)) \land\\{}(orbitValue + \operatorname{orbitOddEnergy}\left(\operatorname{multiplicity}\left(Z, n\right), first, second\right) = \operatorname{orbitEvenEnergy}\left(\operatorname{multiplicity}\left(Z, n\right), first, second\right)) \land\\{}(0 \leq \operatorname{orbitEvenEnergy}\left(\operatorname{multiplicity}\left(Z, n\right), first, second\right))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition.off_line_orbit_parity_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the stated non-self-conjugate off-line orbit, the test seed at the spectral parameter and its conjugate determines even and odd channels. The real four-point convolution-square contribution is their multiplicity-weighted even energy minus odd energy.

Both channel energies are nonnegative, so adding the odd correction recovers the even energy. The result is conditional on the supplied zero data and does not assert existence of an off-line orbit or a prime-side realization of the correction.

## References

- Truth anchor: `D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition.off_line_orbit_parity_decomposition`
- Dependency: [D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds](../ZetaBridge/ConvolutionSquareOrbitBounds.md)
