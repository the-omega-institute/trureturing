# Truncated Weil-Square Positivity Criterion

## Abstract

Relative to supplied zero data, nonnegativity of every finite symmetric truncated repository Weil-square zero sum is equivalent to the Riemann hypothesis.

**Theorem 1.1 (Truncated Weil-square positivity implies RH).**

$$\forall Z \in ZeroData,\; \left(\forall T \in \mathbb{R}, g \in WeilTestFunction,\; 0 \le \Re (\operatorname{truncatedZeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), T\right))\right) \Rightarrow \operatorname{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TruncatedWeilSquarePositivityCriterion.truncatedWeilSquarePositivity_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero in the open right half-strip is represented by the supplied ZeroData. At the cutoff equal to its spectral radius, the frozen off-line separator gives a negative truncated Weil-square sum, contradicting universal nonnegativity. The frozen right-half-strip reduction then gives RH.

**Theorem 1.2 (RH implies truncated Weil-square positivity).**

$$\forall Z \in ZeroData,\; \operatorname{RiemannHypothesis} \Rightarrow \left(\forall T \in \mathbb{R}, g \in WeilTestFunction,\; 0 \le \Re (\operatorname{truncatedZeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), T\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TruncatedWeilSquarePositivityCriterion.rh_implies_truncatedWeilSquarePositivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH, the frozen critical-line bridge turns the critical-line filter of every symmetric cutoff into the whole cutoff. The frozen finite convolution-square theorem then supplies nonnegativity.

**Theorem 1.3 (RH is equivalent to truncated Weil-square positivity).**

$$\forall Z \in ZeroData,\; \operatorname{RiemannHypothesis} \Leftrightarrow \left(\forall T \in \mathbb{R}, g \in WeilTestFunction,\; 0 \le \Re (\operatorname{truncatedZeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), T\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TruncatedWeilSquarePositivityCriterion.rh_iff_truncatedWeilSquarePositivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence is relative to a supplied ZeroData. It does not assert that ZeroData exists; the M1-b existence obligation remains open.

truncatedZeroSum is a sum over symmetricIndices T, exactly the zeros with spectralRadius at most T. This is a finite set, so the statement has no convergence obligation.

This is the repository's positivity criterion, not Weil's literal criterion. Since it is conditional on supplied zero data, the equivalence is not an unconditional proof of RH.

## References

- Truth anchor: `D5/S3/Weil/Separator/TruncatedWeilSquarePositivityCriterion.rh_iff_truncatedWeilSquarePositivity`
- Truth anchor: `D5/S3/Weil/Separator/TruncatedWeilSquarePositivityCriterion.rh_implies_truncatedWeilSquarePositivity`
- Truth anchor: `D5/S3/Weil/Separator/TruncatedWeilSquarePositivityCriterion.truncatedWeilSquarePositivity_implies_rh`
- Dependency: [D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare](OffLineZeroNegativeWeilSquare.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine](../ZetaBridge/ConvolutionSquareCriticalLine.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RhLocatesZeroData](../ZetaBridge/RhLocatesZeroData.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../ZetaBridge/RightHalfStripRiemannReduction.md)
