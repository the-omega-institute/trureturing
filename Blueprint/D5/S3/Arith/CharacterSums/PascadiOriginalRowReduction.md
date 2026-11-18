# The sharper original row reduction

## Abstract

The actual nonunit-row reduction requires only 3Y<p^2, preserving the original scalar-center width range.

**Theorem 1.1 (Keep the original six-width condition after interval doubling).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalRowReduction.Nminus_le_three_Uminus_of_three_width`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalRowReduction.Nminus_le_three_Uminus_of_three_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p, natural literal widths X<=Y with 3Y<p^2, and the same fixed alternating coefficient units a1,a2 modulo p^3, the actual original counts satisfy Nminus<=3*Uminus+8*(2Y+1)^2. The counts are exactly the existing literal integer-box sixReturnWord counts, including all zero rows, mixed nonunit patterns and repeated endpoints. No row-count supplier is assumed.

Reuse divisible_row_count, whose actual pivot and zero-row injections already need only 3X,3Y<p^2. For k=floor(Y/p), the sharper width inequality gives 3k<p. If k is positive, p>=3k+1, k^2>=k and kp<=Y prove (2k+1)^2<=2Y+1; the k=0 case is direct. Thus each divisible row costs at most four square interval lengths. Transpose rows for the second-row bound, and use the original cyclic rotations and unit-column theorem to cover all remaining actual tuples by the three unit-middle charts. The sharpened normalization is the genuine improvement over the existing six-width API.

The scalar-center comparison doubles X,Y. This theorem then requires 3*(2Y)<p^2, exactly the original 6Y<p^2 hypothesis, without introducing a 12Y restriction. It is the nonunit-row reduction only; the unit-middle estimate and final scalar-center sum are separate obligations.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalRowReduction.Nminus_le_three_Uminus_of_three_width`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiMinusRows](PascadiMinusRows.md)
