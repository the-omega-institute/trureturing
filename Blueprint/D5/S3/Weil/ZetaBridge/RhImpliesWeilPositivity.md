# RH Implies the Transcribed O-6 Weil Positivity Statement

## Abstract

The Riemann hypothesis implies the transcribed O-6 Weil positivity statement for every supplied zero data set and Weil test function.

**Theorem 1.1 (RH implies the transcribed O-6 Weil positivity statement).**

$$\operatorname{RiemannHypothesis} \Rightarrow \forall Z: \operatorname{ZeroData}, \forall g: \operatorname{WeilTestFunction}, \forall hZero: \operatorname{SymmetricConvergent}\left(Z, \operatorname{convolutionSquare}\left(g\right)\right), 0 \leq \Re(\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), hZero\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/RhImpliesWeilPositivity.riemannHypothesis_implies_o6WeilPositivityStatement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the verbatim unfolding of Hearts o6WeilPositivityStatement. Hearts is an OPEN X_Frontier source, not a frozen declaration, and a freezable module cannot import X_Frontier. The proposition body is therefore transcribed while the atom's theorem name is preserved verbatim.

Under RH, the frozen R-E bridge puts every supplied ZeroData zero on the critical line. The frozen finite convolution-square theorem makes every truncated real sum nonnegative, and truncatedZeroSum_tendsto plus closedness of the nonnegative ray passes that inequality to zeroSum.

The route volume names truncatedCriticalConvolutionSquareSum_re_nonnegative, which does not exist; the actual frozen theorem is critical_line_truncated_sum_real_nonnegative. Its proposed critical_offline_split_tendsto_explicit_formula route also requires an extra ArchimedeanConvergent hypothesis, so the proof instead uses the symmetric zero-sum limit and closedness.

The theorem holds even when ZeroData is empty. It is not advertised as a non-vacuous Weil positivity result.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/RhImpliesWeilPositivity.riemannHypothesis_implies_o6WeilPositivityStatement`
- Dependency: [D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine](ConvolutionSquareCriticalLine.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RhLocatesZeroData](RhLocatesZeroData.md)
