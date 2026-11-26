# The polynomial extension and integer lemniscatic section jets

## Abstract

The two polynomial variables carry the logarithmic derivative and the section factor.

**Theorem 1.1 (The quotient by S at every order).**

Lean statement: `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.extendedIter_s_multiple`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.extendedIter_s_multiple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product rule updates the quotient inside the coefficient ring by adding hZ times the previous quotient.

**Theorem 1.2 (The zeroth section jet).**

Lean statement: `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.jet_zero_order`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.jet_zero_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation gives one in the zeroth column and zero in every positive column.

**Theorem 1.3 (The all-order product rule).**

Lean statement: `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.iterated_leibniz`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.iterated_leibniz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiation and Pascal’s identity give the binomial convolution of the two lists of derivatives.

**Theorem 1.4 (Restriction to the curve).**

Lean statement: `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.restricted_base`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.restricted_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The iterate preserves the embedded base and agrees there with the original prime operator.

## References

- Truth anchor: `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.extendedIter_s_multiple`
- Truth anchor: `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.iterated_leibniz`
- Truth anchor: `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.jet_zero_order`
- Truth anchor: `D5/S3/Arith/CMJet/ActualRestrictedRecurrence.restricted_base`
- Dependency: [D5/S3/Arith/CMJet/Integral](Integral.md)
