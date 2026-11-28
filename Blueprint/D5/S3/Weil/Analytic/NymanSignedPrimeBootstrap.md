# A centered prime-dilation criterion for the Riemann hypothesis

## Abstract

A centered prime-dilation criterion for the Riemann hypothesis

**Theorem 1.1 (Centering by the integer counting weight).**

Lean statement: `D5/S3/Weil/Analytic/NymanPrimeDilations.primeDilations_add_shell_eq_centered`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanPrimeDilations.primeDilations_add_shell_eq_centered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Möbius inversion evaluates the sum of all integer dilations of the shell. At scales at least one, subtracting the integer counting weight from the prime logarithm weight changes the prime sum by exactly one copy of the shell.

**Theorem 1.2 (The logarithmic correction on earlier scales).**

Lean statement: `D5/S3/Weil/Analytic/NymanLogCorrectionEnvelope.abs_logCorrection_le_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanLogCorrectionEnvelope.abs_logCorrection_le_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic moment of the four-box kernel is a sum of exponentially weighted dilations and integrals. For a power envelope with exponent at least one half, these operations cost at most four times log(7/6) plus sixteen.

**Theorem 1.3 (Equivalence with a one-sided prime bound).**

Lean statement: `D5/S3/Weil/Analytic/NymanSignedPrimeBootstrap.rh_iff_signedPrimeSquareRoot`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanSignedPrimeBootstrap.rh_iff_signedPrimeSquareRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Riemann hypothesis holds exactly when the adverse part of the centered prime-dilation sum is eventually bounded by a constant times x to the power one half plus epsilon, times log x, for every positive epsilon. At each scale the sign comes from the Möbius shell at that scale. The prime-power and kernel corrections are absorbed by the running power envelope.

## References

- Truth anchor: `D5/S3/Weil/Analytic/NymanLogCorrectionEnvelope.abs_logCorrection_le_envelope`
- Truth anchor: `D5/S3/Weil/Analytic/NymanPrimeDilations.primeDilations_add_shell_eq_centered`
- Truth anchor: `D5/S3/Weil/Analytic/NymanSignedPrimeBootstrap.rh_iff_signedPrimeSquareRoot`
- Dependency: [D5/S3/Weil/Analytic/NymanFixedScalarUpper](NymanFixedScalarUpper.md)
