# Off-Line Zero Negative Weil Square

## Abstract

The stored nontriviality of every ZeroData zero discharges nonreality and yields the final full and finite-cutoff off-line Weil-square separators.

**Theorem 1.1 (Stored nontrivial zeros have nonzero imaginary part).**

$$\forall Z \in ZeroData, n \in \mathbb{N},\; \operatorname{Im} (\operatorname{zero}\left(Z, n\right)) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare.zeroData_im_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ZeroData.zero_isNontrivial supplies the stored zero's nontriviality. The frozen alternating-zeta nonreality theorem then rules out a zero imaginary part.

**Theorem 1.2 (An off-line stored zero yields a negative full Weil-square zero sum).**

$$\forall Z \in ZeroData, n \in \mathbb{N},\; \Re (\operatorname{zero}\left(Z, n\right)) \ne criticalAbscissa \Rightarrow \left(\exists g \in WeilTestFunction, hZero \in \operatorname{SymmetricConvergent}\left(Z, \operatorname{convolutionSquare}\left(g\right)\right),\; \Re (\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), hZero\right)) < 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare.offLineZero_yields_negative_weil_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The addressable nonreality theorem discharges hIm in the frozen off-line nonreal separator. Thus every stored off-line nontrivial zero gives a Weil test function whose convolution square has strictly negative full zero-sum real part.

This final separator does not prove that O-6 implies the Riemann hypothesis and does not assert that ZeroData is inhabited; the M1-b inhabitance obligation remains open.

**Theorem 1.3 (An off-line stored zero in a cutoff yields a negative truncated Weil square).**

$$\forall Z \in ZeroData, n \in \mathbb{N}, T \in \mathbb{R},\; \left(n \in \operatorname{symmetricIndices}\left(Z, T\right) \land \Re (\operatorname{zero}\left(Z, n\right)) \ne criticalAbscissa\right) \Rightarrow \left(\exists g \in WeilTestFunction,\; \Re (\operatorname{truncatedZeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), T\right)) < 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare.offLineZero_negative_truncated_weil_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an index in the symmetric cutoff, the same addressable nonreality theorem discharges hIm in the frozen finite-cutoff separator. The conclusion concerns only the truncated zero sum.

## References

- Truth anchor: `D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare.offLineZero_negative_truncated_weil_square`
- Truth anchor: `D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare.offLineZero_yields_negative_weil_square`
- Truth anchor: `D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare.zeroData_im_ne_zero`
- Dependency: [D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation](../ZetaBridge/AlternatingZetaContinuation.md)
- Dependency: [D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare](../ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.md)
- Dependency: [D5/S3/Weil/ZetaBridge/OffLineZeroNegativeTruncatedWeilSquare](../ZetaBridge/OffLineZeroNegativeTruncatedWeilSquare.md)
