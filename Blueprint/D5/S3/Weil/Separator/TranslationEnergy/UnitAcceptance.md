# Acceptance of the rounded unit producer

## Abstract

Acceptance of the rounded unit producer.

**Theorem 1.1 (Every actual source cell).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/UnitAcceptance.check_unitPolynomialPayload`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/UnitAcceptance.check_unitPolynomialPayload` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural radius R, rational shift s, any mesh depth d and scalar precision m, the rounded payload for each actual source cell passes the canonical checker at Taylor depth 4m+4. Both polynomial components are the constant one.

Cutoff endpoints are rounded outwards to multiples of 2^-32. The signed differences and squares retain checker acceptance.

**Theorem 1.2 (List and cell alignment).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/UnitAcceptance.unitPolynomialPayloads_cells_accepted`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/UnitAcceptance.unitPolynomialPayloads_cells_accepted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping this producer over sourceCells gives exactly one payload per adjacent source pair. The mapped list has the required first and last hull endpoints, each index retrieves its actual cell payload, and every cell check in the full Boolean conjunction succeeds.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/UnitAcceptance.check_unitPolynomialPayload`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/UnitAcceptance.unitPolynomialPayloads_cells_accepted`
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Integral](Integral.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Scalar/Uniform](Scalar/Uniform.md)
