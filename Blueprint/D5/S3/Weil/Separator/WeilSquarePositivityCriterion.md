# Weil-Square Positivity Criterion

## Abstract

Relative to supplied zero data, nonnegativity of every repository Weil-square zero sum implies the Riemann hypothesis and is equivalent to it.

**Theorem 1.1 (Weil-square positivity implies the Riemann hypothesis).**

$$\forall Z \in ZeroData,\; \left(\forall g \in WeilTestFunction, hZero \in \operatorname{SymmetricConvergent}\left(Z, \operatorname{convolutionSquare}\left(g\right)\right),\; 0 \le \Re (\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), hZero\right))\right) \Rightarrow \operatorname{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/WeilSquarePositivityCriterion.weilSquarePositivity_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero in the open right half-strip is a nontrivial zero and is therefore represented by the supplied ZeroData. The frozen off-line separator produces a convolution square with negative zero-sum real part, contradicting the assumed nonnegativity.

The frozen right-half-strip reduction turns that exclusion into the Riemann hypothesis. No separator or zeta-reduction fact is reproved here.

**Theorem 1.2 (RH is equivalent to Weil-square positivity).**

$$\forall Z \in ZeroData,\; \operatorname{RiemannHypothesis} \Leftrightarrow \left(\forall g \in WeilTestFunction, hZero \in \operatorname{SymmetricConvergent}\left(Z, \operatorname{convolutionSquare}\left(g\right)\right),\; 0 \le \Re (\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), hZero\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/WeilSquarePositivityCriterion.rh_iff_weilSquarePositivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse implication is the preceding separator argument. The forward implication is the frozen RH-to-positivity theorem.

Both statements are relative to a supplied ZeroData; this module does not assert that ZeroData exists, and the M1-b existence obligation remains open.

The right side is positivity for this repository's zeroSum, convolutionSquare, and WeilTestFunction definitions. It is not a literal transcription of Weil's explicit-formula criterion, and the conditional equivalence is not an unconditional proof of RH.

## References

- Truth anchor: `D5/S3/Weil/Separator/WeilSquarePositivityCriterion.rh_iff_weilSquarePositivity`
- Truth anchor: `D5/S3/Weil/Separator/WeilSquarePositivityCriterion.weilSquarePositivity_implies_rh`
- Dependency: [D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare](OffLineZeroNegativeWeilSquare.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RhImpliesWeilPositivity](../ZetaBridge/RhImpliesWeilPositivity.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../ZetaBridge/RightHalfStripRiemannReduction.md)
