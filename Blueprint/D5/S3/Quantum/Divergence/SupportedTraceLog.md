# Supported trace-log joint convexity

## Abstract

Finite joint convexity for supported PSD trace-log pairings.

**Theorem 1.1 (Joint convexity for arbitrary finite masses).**

Lean statement: `D5/S3/Quantum/Divergence/SupportedTraceLog.traceLog_jointConvex`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/SupportedTraceLog.traceLog_jointConvex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Supported joint convexity and the Fibonacci mixed-qubit margin*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Take finite matrix and family index types, nonnegative common weights wᵢ, and positive semidefinite pairs Sᵢ and Tᵢ with ker Tᵢ contained in ker Sᵢ. For D(S,T) = Re Tr[S(log S − log T)], the pairing of the two weighted sums is bounded by the weighted sum of the individual pairings. The spectral logarithm takes the value zero at eigenvalue zero. Both sides vanish when either index type is empty.

When the numerator sum is nonzero, both aggregate traces are positive. Normalize each family by its own aggregate trace and apply the flag-erasure log-sum inequality. The support projections absorb the logarithmic scale corrections, and trace additivity cancels the common correction. A zero numerator sum forces every weighted numerator block to vanish. The same-scale identity includes vanishing weights.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/SupportedTraceLog.traceLog_jointConvex`
- Dependency: [D5/S3/Quantum/Divergence/FannesRootFidelityHolevo](FannesRootFidelityHolevo.md)
