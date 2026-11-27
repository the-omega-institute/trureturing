# Fibonacci mixed qubit bound

## Abstract

The quantitative Fibonacci trace-log gap for three mixed qubit preparations.

**Theorem 1.1 (Quantitative bound below the benchmark).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/FibonacciMixedQubit.traceLog_le_benchmark_sub_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/Qubit/FibonacciMixedQubit.traceLog_le_benchmark_sub_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Supported joint convexity and the Fibonacci mixed-qubit margin*. URL: <https://github.com/the-omega-institute/trureturing>.

*Acknowledgement.* trureturing research synthesis (2026). *Six-interval certificate for the Fibonacci pure-qubit profile*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Take three complex two-by-two positive semidefinite matrices X₁, X₂, X₃, each of trace one. Form A with weights (88, 25, 28)/141 and C with weights (66, 15, 12)/141. The real trace of A(log A − log C) is at most (113/141) log(113/81) + (28/141) log(7/3) − (3(1 − Re Tr(X₁X₂)) + 11 Re Tr(X₁X₃))/63360. The spectral logarithm takes the value zero at eigenvalue zero.

Independently sample one rank-one spectral projection from each preparation with its eigenvalue as weight. The one-coordinate marginals recover both matrix mixtures. The two-coordinate marginals recover the two real trace overlaps in the deficit. Apply supported joint convexity, then average the pure-qubit bound with the full product weights. Positive reference coefficients guarantee kernel inclusion on each spectral choice, including singular references. Zero eigenvalues contribute zero through the homogeneous joint-convexity formula.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/FibonacciMixedQubit.traceLog_le_benchmark_sub_margin`
- Dependency: [D5/S3/Quantum/Divergence/FannesRootFidelityHolevo](../FannesRootFidelityHolevo.md)
- Dependency: [D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile](FibonacciClippedProfile.md)
- Dependency: [D5/S3/Quantum/Divergence/Qubit/SignedProfile](SignedProfile.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportedTraceLog](../SupportedTraceLog.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzSpectralCoordinates](../../Recovery/PetzSpectralCoordinates.md)
