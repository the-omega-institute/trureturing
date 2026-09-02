# Off-Line Zero Negative Truncated Weil Square

## Abstract

An off-line nonreal zero inside a symmetric cutoff separates the truncated Weil form.

**Theorem 1.1 (A finite-cutoff separator from one off-line nonreal zero).**

$$\forall Z: ZeroData, n: \mathbb{N}, T: \mathbb{R},\\{}(((n \in \operatorname{symmetricIndices}\left(Z, T\right)) \land (\Re (\operatorname{zero}\left(Z, n\right)) \neq criticalAbscissa)) \land (\operatorname{Im} (\operatorname{zero}\left(Z, n\right)) \neq 0)) \Rightarrow (\exists g: WeilTestFunction, \Re (\operatorname{truncatedZeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), T\right)) < 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OffLineZeroNegativeTruncatedWeilSquare.offLineZero_yields_negative_truncated_weil_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the lesser index in each reflection pair inside the symmetric cutoff. These representatives have distinct frequencies even up to sign, so finite even interpolation prescribes opposite unit values on the target conjugate pair and zero on every other pair.

The convolution-square summands outside the target four-point orbit then vanish. The frozen prescribed-pair orbit identity makes the remaining real sum minus four times the positive stored multiplicity.

This is only a finite-cutoff statement. It asserts nothing about limits, SymmetricConvergent, or zeroSum; the nonzero imaginary-part hypothesis is the explicit M3-d input.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/OffLineZeroNegativeTruncatedWeilSquare.offLineZero_yields_negative_truncated_weil_square`
- Dependency: [D5/S3/Weil/TestFunctions/EvenTestFunctionFiniteInterpolation](../TestFunctions/EvenTestFunctionFiniteInterpolation.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PrescribedPairNegativeOrbit](PrescribedPairNegativeOrbit.md)
