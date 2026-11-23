# Bounds for divided difference coefficients

## Abstract

Bounds for divided difference coefficients

**Theorem 1.1 (Bounds for divided difference coefficients).**

Lean statement: `D5/S3/Arith/Additive/Waring/WaringCoeffBound.diffCoeff_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/Waring/WaringCoeffBound.diffCoeff_bound` (`✓ std3`). ∎

*Citation.* The Waring formalization authors (2026). *Waring's theorem in Lean 4*. URL: <https://github.com/yunyougu50-create/waring-lean4/tree/cd0735c253f3b640262fcc74a61306cb41e23765>.

*Commentary.*

For shifts bounded by N, each divided difference coefficient below degree d is bounded by the original coefficient bound times a binomial sum and N to the corresponding reduced degree.

**Theorem 1.2 (Polynomial finite differences).**

Lean statement: `D5/S3/Arith/Additive/Waring/WaringCoeffBound.diffH_polyEval`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/Waring/WaringCoeffBound.diffH_polyEval` (`✓ std3`). ∎

*Citation.* The Waring formalization authors (2026). *Waring's theorem in Lean 4*. URL: <https://github.com/yunyougu50-create/waring-lean4/tree/cd0735c253f3b640262fcc74a61306cb41e23765>.

*Commentary.*

The step-h difference of an integer polynomial is h times the polynomial with the divided difference coefficients.

## References

- Truth anchor: `D5/S3/Arith/Additive/Waring/WaringCoeffBound.diffCoeff_bound`
- Truth anchor: `D5/S3/Arith/Additive/Waring/WaringCoeffBound.diffH_polyEval`
