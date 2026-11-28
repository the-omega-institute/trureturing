# The first logarithmic moment

## Abstract

The first logarithmic moment of centered prime dilations

**Theorem 1.1 (The exact first logarithmic moment).**

Lean statement: `D5/S3/Weil/Analytic/NymanCenteredLogMoment.integral_centeredPrime_log_weighted`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanCenteredLogMoment.integral_centeredPrime_log_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral of the centered prime sum times log x divided by x squared equals the ordinary kernel moment times twice the Euler–Mascheroni constant plus the higher prime power series at one minus one. The pole terms from the zeta function and its logarithmic derivative cancel in the centered Dirichlet series. Absolute integrability with the extra logarithm permits passage to the right difference quotient.

**Theorem 1.2 (Strict positivity of the moment).**

Lean statement: `D5/S3/Weil/Analytic/NymanCenteredLogMoment.integral_centeredPrime_log_weighted_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanCenteredLogMoment.integral_centeredPrime_log_weighted_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed kernel moment is positive. The higher prime power series is nonnegative, and the Euler–Mascheroni constant exceeds one half.

## References

- Truth anchor: `D5/S3/Weil/Analytic/NymanCenteredLogMoment.integral_centeredPrime_log_weighted`
- Truth anchor: `D5/S3/Weil/Analytic/NymanCenteredLogMoment.integral_centeredPrime_log_weighted_pos`
- Dependency: [D5/S3/Weil/Analytic/NymanCenteredMoment](NymanCenteredMoment.md)
