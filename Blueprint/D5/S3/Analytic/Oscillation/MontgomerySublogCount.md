# Montgomery sums with sublogarithmic counting error

## Abstract

An error smaller than the logarithmic scale suffices for the leading upper coefficient.

Write c = 1/(2π) and M(Y) = cY(log(cY)−1). Let N(Y) count all multiplicities through the inclusive cutoff. Assume (N(Y)−M(Y))/log Y tends to zero.

**Theorem 1.1 (The leading count).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomerySublogCount.countAsymptotic_of_sublog`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomerySublogCount.countAsymptotic_of_sublog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ratio N(Y)/(Y log Y) tends to c. The rescaled discrepancy tends to zero and the main term supplies the limit.

**Theorem 1.2 (A uniform leading upper coefficient).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomerySublogCount.pairSum_le_of_sublog_discrepancy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomerySublogCount.pairSum_le_of_sublog_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every ε > 0 and all sufficiently large Y, the inclusive ordered Lorentz pair sum at every real phase parameter is at most (2πc²+ε)Y(log Y)².

Given η > 0, choose A so that the absolute count error is at most η log Y at every height from A through Y. Pad the left endpoint by 1/log Y and charge the early ordinates to N(A). The two endpoint errors are at most 2η log Y in total. Integration over the Lorentz kernel's superlevel intervals bounds each row, and the leading count converts the result into the uniform coefficient.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomerySublogCount.countAsymptotic_of_sublog`
- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomerySublogCount.pairSum_le_of_sublog_discrepancy`
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryCountUpper](MontgomeryCountUpper.md)
- Dependency: [D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff](SpectrumPhaseCutoff.md)
