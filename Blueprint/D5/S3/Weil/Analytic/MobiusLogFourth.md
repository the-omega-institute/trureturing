# A Mertens bound from the centered Mangoldt recurrence

## Abstract

An unconditional fourth-logarithmic bound for the Mertens function

**Theorem 1.1 (The centered finite recurrence).**

Lean statement: `D5/S3/Weil/Analytic/MobiusCenteredHyperbola.sum_log_weighted_moebius`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/MobiusCenteredHyperbola.sum_log_weighted_moebius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the constant counting weight from von Mangoldt gives a logarithmic Möbius convolution with one boundary unit. A finite Dirichlet hyperbola split writes this convolution as a short sum of Möbius prefixes and a tail involving only differences of the centered Mangoldt prefix.

**Theorem 1.2 (Fourth-logarithmic decay for ordinary Möbius prefixes).**

Lean statement: `D5/S3/Weil/Analytic/MobiusLogFourth.mobiusPrefix_fourth_log_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/MobiusLogFourth.mobiusPrefix_fourth_log_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x greater than one, the absolute Möbius prefix is bounded by a constant times x divided by the fourth power of log x. The medium prime number theorem controls the tail at the eighth-root cutoff. Discrete Abel summation and the short head give a contraction of the running normalized envelope.

## References

- Truth anchor: `D5/S3/Weil/Analytic/MobiusCenteredHyperbola.sum_log_weighted_moebius`
- Truth anchor: `D5/S3/Weil/Analytic/MobiusLogFourth.mobiusPrefix_fourth_log_bound`
