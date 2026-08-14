# Convolution-Square Critical-Line Split

## Abstract

Symmetric convolution-square zero cutoffs split into a nonnegative critical-line part and an off-line remainder without asserting the Riemann hypothesis.

**Theorem 1.1 (The spectral parameter is real exactly on the critical line).**

$$\forall Z: \operatorname{ZeroData}, \forall n\in \mathbb{N}, \operatorname{Im}(Z.gamma(n)) = 0 \Leftrightarrow \Re(Z.zero(n)) = \operatorname{criticalAbscissa}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.gamma_im_eq_zero_iff_zero_on_critical_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every index in supplied ZeroData, the imaginary part of its complex spectral parameter vanishes exactly when the corresponding zero has real part equal to the critical abscissa. This is an algebraic consequence of the frozen spectral-parameter definition and makes no claim that every zero satisfies the condition.

**Theorem 1.2 (A critical-line zero summand is real and nonnegative).**

$$\forall Z: \operatorname{ZeroData}, g\in \mathcal{W}, n\in \mathbb{N}, \Re(Z.zero(n)) = \operatorname{criticalAbscissa} \Rightarrow \operatorname{Im}(\operatorname{zeroSummand}(Z, \operatorname{convolutionSquare}(g), n)) = 0 \land 0 \leq \Re(\operatorname{zeroSummand}(Z, \operatorname{convolutionSquare}(g), n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.critical_line_zero_summand_real_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the critical line, the preceding equivalence identifies gamma with its real part. The frozen convolution-square positivity theorem then makes the Fourier-Laplace factor real and nonnegative. Multiplication by the stored natural-number zero multiplicity preserves both conclusions.

**Theorem 1.3 (Every critical-line truncated sum is real and nonnegative).**

$$\forall Z: \operatorname{ZeroData}, g\in \mathcal{W}, T\in \mathbb{R}, \operatorname{Im}(\operatorname{criticalPart}(Z, g, T)) = 0 \land 0 \leq \Re(\operatorname{criticalPart}(Z, g, T))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.critical_line_truncated_sum_real_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here criticalPart is the finite sum over symmetricIndices T filtered by real part equal to criticalAbscissa, with each term equal to zeroSummand of the convolution square. Complex real and imaginary parts commute with finite sums, so termwise realness and nonnegativity give the two claims.

**Theorem 1.4 (A finite zero sum splits into critical and off-line parts).**

$$\forall Z: \operatorname{ZeroData}, g\in \mathcal{W}, T\in \mathbb{R}, \operatorname{truncatedZeroSum}(Z, \operatorname{convolutionSquare}(g), T) = \operatorname{criticalPart}(Z, g, T) + \operatorname{offlinePart}(Z, g, T)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.truncated_zero_sum_critical_offline_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The criticalPart filter uses equality with criticalAbscissa and offlinePart uses its negation on the same symmetric finite index set. Mathlib's finite filter-complement identity partitions the complete truncated zero sum. No assertion is made about either filtered family converging separately.

**Theorem 1.5 (The combined split tends to the explicit-formula value).**

$$\forall Z: \operatorname{ZeroData}, g\in \mathcal{W}, hZero, hArch, \lim_{T\to\infty} (\operatorname{criticalPart}(Z, g, T) + \operatorname{offlinePart}(Z, g, T)) = \operatorname{poleTerm}(\operatorname{convolutionSquare}(g)) - \operatorname{primeTerm}(\operatorname{convolutionSquare}(g)) + \operatorname{archimedeanTerm}(\operatorname{convolutionSquare}(g), hArch)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.critical_offline_split_tendsto_explicit_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assuming only the frozen symmetric-zero and archimedean convergence premises for the convolution square, the combined filtered expression is rewritten to truncatedZeroSum. Its existing limit and the Weil explicit formula identify the displayed pole-minus-prime-plus-archimedean value. The theorem supplies no separate convergence result for either filter and does not assert the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.critical_line_truncated_sum_real_nonnegative`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.critical_line_zero_summand_real_nonnegative`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.critical_offline_split_tendsto_explicit_formula`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.gamma_im_eq_zero_iff_zero_on_critical_line`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.truncated_zero_sum_critical_offline_split`
- Dependency: [D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity](../TestFunctions/ConvolutionSquarePositivity.md)
