# Height-Window Weil-Square Criterion

## Abstract

Relative to supplied zero data, critical-line location in every spectral-radius window is characterized by truncated Weil-square positivity, and the all-height condition is equivalent to RH.

**Theorem 1.1 (Critical-line location in a height window is equivalent to positivity).**

$$\forall Z \in ZeroData, T \in \mathbb{R},\; \left(\forall n \in \mathbb{N},\; n \in \operatorname{symmetricIndices}\left(Z, T\right) \Rightarrow \Re (\operatorname{zero}\left(Z, n\right)) = criticalAbscissa\right) \Leftrightarrow \left(\forall g \in WeilTestFunction,\; 0 \le \Re (\operatorname{truncatedZeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), T\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/HeightWindowWeilSquareCriterion.heightWindow_rh_iff_truncatedWeilSquarePositivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward implication identifies the critical-line filter with the full finite cutoff and applies the frozen critical-line truncated-sum nonnegativity theorem. The reverse implication uses the frozen finite-cutoff separator: any off-line index would produce a strictly negative truncated Weil square.

The height window is the spectral-radius condition norm(Z.gamma n) <= T, not a bound on the imaginary part of a zero. Positivity means this repository's truncatedZeroSum and convolutionSquare positivity.

**Theorem 1.2 (RH is equivalent to critical-line location at every height).**

$$\forall Z \in ZeroData,\; \operatorname{RiemannHypothesis} \Leftrightarrow \left(\forall T \in \mathbb{R},\; \forall n \in \mathbb{N},\; n \in \operatorname{symmetricIndices}\left(Z, T\right) \Rightarrow \Re (\operatorname{zero}\left(Z, n\right)) = criticalAbscissa\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/HeightWindowWeilSquareCriterion.rh_iff_forall_heightWindow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH locates every zero represented by the supplied ZeroData on the critical line. Conversely, exhaustiveness places any zero in the spectral-radius window at its own radius, and the frozen right-half-strip reduction then yields RH.

Both equivalences are relative to a supplied ZeroData; this document does not assert that ZeroData exists, and the M1-b existence obligation remains open. The result is not an unconditional proof of the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Separator/HeightWindowWeilSquareCriterion.heightWindow_rh_iff_truncatedWeilSquarePositivity`
- Truth anchor: `D5/S3/Weil/Separator/HeightWindowWeilSquareCriterion.rh_iff_forall_heightWindow`
- Dependency: [D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare](OffLineZeroNegativeWeilSquare.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine](../ZetaBridge/ConvolutionSquareCriticalLine.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RhLocatesZeroData](../ZetaBridge/RhLocatesZeroData.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../ZetaBridge/RightHalfStripRiemannReduction.md)
