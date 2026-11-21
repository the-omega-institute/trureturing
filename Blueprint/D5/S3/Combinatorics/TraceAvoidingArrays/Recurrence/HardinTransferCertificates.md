# Continuation polynomials

## Abstract

The source vector identities with exact integer lags.

**Theorem 1.1 (Full-state relation at height 1).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowOne`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On all 3 unrestricted columns at height 1, the power at exponent 3 on ones equals the source lag-weighted sum of the power vectors at exponents 2 down to 1. The coefficient sum is one. The coefficients are (3, −2).

**Definition 1.2 (Source lag coefficients).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowTwoCoefficients`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowTwoCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficients at lags one through 3 are (3, 0, −2).

**Theorem 1.3 (Full-state relation at height 2).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowTwo`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On all 9 unrestricted columns at height 2, the power at exponent 4 on ones equals the source lag-weighted sum of the power vectors at exponents 3 down to 1. The coefficient sum is one.

**Definition 1.4 (Source lag coefficients).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowThreeCoefficients`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowThreeCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficients at lags one through 4 are (4, 1, −6, 2).

**Theorem 1.5 (Full-state relation at height 3).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowThree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowThree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On all 27 unrestricted columns at height 3, the power at exponent 5 on ones equals the source lag-weighted sum of the power vectors at exponents 4 down to 1. The coefficient sum is one.

**Theorem 1.6 (Full-state relation at width 2).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordTwo`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On all 6 proper words at width 2, the power at exponent 2 on ones equals the source lag-weighted sum of the power vectors at exponents 1 down to 0. The coefficient sum is one. The coefficients are (4, −3). The diagonal and vertical-bond square matrices each satisfy this identity.

**Definition 1.7 (Source lag coefficients).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordThreeCoefficients`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordThreeCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficients at lags one through 3 are (6, −7, 2).

**Theorem 1.8 (Full-state relation at width 3).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordThree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordThree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On all 12 proper words at width 3, the power at exponent 3 on ones equals the source lag-weighted sum of the power vectors at exponents 2 down to 0. The coefficient sum is one. The diagonal and vertical-bond square matrices each satisfy this identity.

**Definition 1.9 (Source lag coefficients).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordFourCoefficients`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordFourCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficients at lags one through 3 are (8, −11, 4).

**Theorem 1.10 (Full-state relation at width 4).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordFour`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordFour` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On all 24 proper words at width 4, the power at exponent 3 on ones equals the source lag-weighted sum of the power vectors at exponents 2 down to 0. The coefficient sum is one.

**Theorem 1.11 (The two-row quadratic relation).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowTwoRadical`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowTwoRadical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all nine columns, applying C²−2C−2I to ones gives the zero vector. The identity uses exponent zero on every column and supplies the source radical formula.

For each source state, the allowed labels at each successor position exclude the labels on all incident cross-bonds. For a proper-word transfer also require adjacent successor labels to differ. Horner evaluation of the integer relation verifies the zero residual at every actual state.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowOne`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowThree`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowThreeCoefficients`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowTwo`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowTwoCoefficients`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.rowTwoRadical`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordFour`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordFourCoefficients`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordThree`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordThreeCoefficients`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordTwo`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers](HardinActualTransfers.md)
