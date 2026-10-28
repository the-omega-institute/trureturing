# SelectedMinorNonzero

## Abstract

Nonvanishing of the selected literal leading minor

The matrix retains the twenty-eight shifted sourceE0/sourceE1 rows in their original order. Its columns are r^28 through r. Thus its determinant is precisely a0 of the fixed-column prescription, including its sign.

An exact FC sign calculation places criticalRoot between 1275805397989720295463228680851631265311/10^40 and the next rational with denominator 10^40. A rational preconditioner with denominator 2^64 has entries bounded in absolute value by 2^79. At the lower endpoint every entry of its product with the literal matrix differs from the identity by at most 1/128.

On the real unit interval, every matrix entry has Lipschitz constant at most 2^35. Moving from the rational endpoint to criticalRoot changes each preconditioned entry by at most 1/128. The resulting error from the identity is at most 1/64 in each entry. Each diagonal entry therefore has absolute value at least 63/64, while the sum of the other twenty-seven absolute values is at most 27/64. Strict diagonal dominance proves that the product, and hence the chosen literal minor, has nonzero determinant.

This argument concerns the original algebraic root and the actual chosen matrix. It does not infer nonvanishing from uniqueness of a common root. The universal complex-root statements and the full original coefficient-world and response-center identifications require further arguments.

**Theorem 1.1 (nonzero chosen minor at the selected FC root).**

Lean statement: `D5/S3/Observer/CubicGain/SelectedMinorNonzero.selected_minor_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/SelectedMinorNonzero.selected_minor_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant of fixedMinorR(literalMatrix(criticalRoot)) is nonzero. This statement has no additional hypotheses; all matrix entries and the selected FC root are the original ones.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/SelectedMinorNonzero.selected_minor_nonzero`
- Dependency: [D5/S3/Observer/CubicGain/SelectedRootCommonZero](SelectedRootCommonZero.md)
