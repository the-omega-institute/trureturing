# The zero-frequency limit

## Abstract

The zero-frequency pair sum attains the leading coefficient under sublogarithmic counting error.

**Theorem 1.1 (The exact zero-frequency coefficient).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomerySublogZeroLimit.tendsto_pairSum_zero_of_sublog_discrepancy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomerySublogZeroLimit.tendsto_pairSum_zero_of_sublog_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write c = 1/(2π). Assume the inclusive count differs from cY(log(cY)−1) by o(log Y). The ordered Lorentz pair sum at zero, divided by Y(log Y)², tends to 2πc².

At zero frequency every difference cosine equals one. The alignment lower bound and the uniform upper bound therefore approach the same coefficient from both sides.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomerySublogZeroLimit.tendsto_pairSum_zero_of_sublog_discrepancy`
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryAlignmentLower](MontgomeryAlignmentLower.md)
- Dependency: [D5/S3/Analytic/Oscillation/MontgomerySublogCount](MontgomerySublogCount.md)
