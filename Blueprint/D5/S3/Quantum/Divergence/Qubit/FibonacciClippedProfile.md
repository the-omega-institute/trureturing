# Fibonacci qubit profile

## Abstract

The clipped Fibonacci qubit profile and trace-log divergence bounds.

**Definition 1.1 (Contrast weights).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.weights`

*Formalization.* `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Six-interval certificate for the Fibonacci pure-qubit profile*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The three real weights are −b, −c, and d, with b = 66t − 88, c = 15t − 25, and d = 28 − 12t.

**Definition 1.2 (Benchmark preparations).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.benchmark`

*Formalization.* `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.benchmark` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Six-interval certificate for the Fibonacci pure-qubit profile*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The first two preparations equal (1, 0) and the third equals (0, 1).

**Definition 1.3 (Time cuts).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.timeCut`

*Formalization.* `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.timeCut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Six-interval certificate for the Fibonacci pure-qubit profile*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The seven endpoints are 4/3, 113/81, 22/15, 5/3, 9/5, 2, and 7/3.

**Definition 1.4 (Affine profile envelopes).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.envelope`

*Formalization.* `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.envelope` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Six-interval certificate for the Fibonacci pure-qubit profile*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Put w = 69t − 85. In increasing interval order the affine expressions are b²X/d + bZ, −bcX/w − (97/100)(b+c)Y − cdZ/w, −bcX/w − bdY/w − cdZ/w, −(53/55)bcX/w − (24/25)bdY/w, −(53/55)bcX/w − (d − (53/55)bc/w)Y, and −dX.

**Theorem 1.5 (Global bound for the excess positive-part trace).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.excess_profile_le_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.excess_profile_le_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Six-interval certificate for the Fibonacci pure-qubit profile*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For every unit complex qubit triple, X is one minus the squared overlap of the first two preparations and Y and Z are their respective squared overlaps with the third. On each closed interval between successive cuts, the actual positive-part trace for the given triple minus that of the benchmark is at most the corresponding envelope. The first interval uses the trace–determinant quadratic, with positive benchmark trace and b ≤ d. For later intervals, each candidate bounds the clipped branch and dominates the square-root branch by a squared inequality. The proof assumes unit normalization and applies also when the preparations are linearly dependent.

**Theorem 1.6 (Quantitative bound below the benchmark).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.traceLog_le_benchmark_sub_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.traceLog_le_benchmark_sub_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Six-interval certificate for the Fibonacci pure-qubit profile*. URL: <https://github.com/the-omega-institute/trureturing>.

*Acknowledgement.* Christoph Hirche and Marco Tomamichel (2024). *Quantum Rényi and f-divergences from integral representations*. DOI: [10.1007/s00220-024-05087-3](https://doi.org/10.1007/s00220-024-05087-3). URL: <https://arxiv.org/abs/2306.12343>.

*Commentary.*

For every triple of unit complex qubit preparations, form A with weights (88, 25, 28)/141 and C with weights (66, 15, 12)/141. Set X to one minus the squared overlap of the first two preparations and Y to the squared overlap of the first and third. The trace-log divergence is at most (113/141) log(113/81) + (28/141) log(7/3) − (3X + 11Y)/63360.

For positive definite C the forward hockey-stick difference identity of Hirche and Tomamichel reduces the comparison to the six clipped profile integrals. The affine logarithmic primitives and five-term rational logarithm bounds certify the coefficients. Orthogonal decomposition of the second vector along the first controls the third squared overlap. For singular C the positive weights force all three preparations onto the same ray and the divergence is log(47/31).

## References

- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.benchmark`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.envelope`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.excess_profile_le_envelope`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.timeCut`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.traceLog_le_benchmark_sub_margin`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.weights`
- Dependency: [D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral](../ForwardHockeyStickIntegral.md)
- Dependency: [D5/S3/Quantum/Divergence/Qubit/SignedProfile](SignedProfile.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation](../../Information/FullwoodParzygnatSubadditivityRefutation.md)
