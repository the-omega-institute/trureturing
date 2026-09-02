# Prescribed-Pair Negative and Real Orbit Values

## Abstract

Opposite prescribed transform values make a nonreal off-line zero orbit negative, while a real off-line orbit is a nonnegative norm square.

**Theorem 1.1 (A prescribed spectral pair makes a nonreal off-line orbit negative).**

$$\forall Z: ZeroData, n: \mathbb{N}, g: WeilTestFunction,\\{}((((\Re (\operatorname{zero}\left(Z, n\right)) \neq criticalAbscissa) \land (\operatorname{Im} (\operatorname{zero}\left(Z, n\right)) \neq 0)) \land (\operatorname{fourierLaplace}\left(g, \operatorname{gamma}\left(Z, n\right)\right) = 1)) \land (\operatorname{fourierLaplace}\left(g, \operatorname{conj}\left(\operatorname{gamma}\left(Z, n\right)\right)\right) = -1)) \Rightarrow (\Re (\sum_{k \in \left\{n, \operatorname{reflection}\left(Z, n\right), \operatorname{conjugation}\left(Z, n\right), \operatorname{conjugation}\left(Z, \operatorname{reflection}\left(Z, n\right)\right)\right\}} \operatorname{zeroSummand}\left(Z, \operatorname{convolutionSquare}\left(g\right), k\right)) = -4 \cdot \operatorname{multiplicity}\left(Z, n\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrescribedPairNegativeOrbit.prescribed_pair_gives_negative_zero_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For supplied ZeroData and a nonreal off-line zero, the conjugation index differs from the original index. The frozen four-point orbit identity and complex-frequency convolution-square factorization reduce the orbit real part to the product of the two prescribed transform values, giving minus four times the stored multiplicity.

**Theorem 1.2 (A real off-line orbit is a nonnegative norm square).**

$$\forall Z: ZeroData, n: \mathbb{N}, g: WeilTestFunction,\\{}((\operatorname{Im} (\operatorname{zero}\left(Z, n\right)) = 0) \land (\Re (\operatorname{zero}\left(Z, n\right)) \neq criticalAbscissa)) \Rightarrow (\Re (\sum_{k \in \left\{n, \operatorname{reflection}\left(Z, n\right), \operatorname{conjugation}\left(Z, n\right), \operatorname{conjugation}\left(Z, \operatorname{reflection}\left(Z, n\right)\right)\right\}} \operatorname{zeroSummand}\left(Z, \operatorname{convolutionSquare}\left(g\right), k\right)) = 2 \cdot \operatorname{multiplicity}\left(Z, n\right) \cdot \operatorname{normSq}\left(\operatorname{fourierLaplace}\left(g, \operatorname{gamma}\left(Z, n\right)\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrescribedPairNegativeOrbit.real_off_line_zero_orbit_sum_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real off-line zero, conjugation fixes both the zero index and its reflected index, while reflection remains distinct. The four displayed indices therefore collapse to a two-point orbit. Frozen reflection, evenness, and factorization identities identify its real value with twice the multiplicity times the transform norm square.

**Theorem 1.3 (Opposite prescribed values are impossible at a real zero).**

$$\forall Z: ZeroData, n: \mathbb{N}, g: WeilTestFunction,\\{}(((\operatorname{Im} (\operatorname{zero}\left(Z, n\right)) = 0) \land (\operatorname{fourierLaplace}\left(g, \operatorname{gamma}\left(Z, n\right)\right) = 1)) \land (\operatorname{fourierLaplace}\left(g, \operatorname{conj}\left(\operatorname{gamma}\left(Z, n\right)\right)\right) = -1)) \Rightarrow (False).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrescribedPairNegativeOrbit.prescribed_pair_impossible_for_real_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reality makes conjugation fix the zero index. Spectral conjugation and evenness then identify the two transform evaluations, so they cannot simultaneously equal one and minus one.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/PrescribedPairNegativeOrbit.prescribed_pair_gives_negative_zero_orbit`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrescribedPairNegativeOrbit.prescribed_pair_impossible_for_real_zero`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrescribedPairNegativeOrbit.real_off_line_zero_orbit_sum_re`
- Dependency: [D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds](ConvolutionSquareOrbitBounds.md)
