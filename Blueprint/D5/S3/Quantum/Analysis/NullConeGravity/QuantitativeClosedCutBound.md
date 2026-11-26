# Quantitative closed-cut bounds

## Abstract

Sharp weighted cycle variance, quantitative finite-anchor dimension bounds, and signed joint-cut tail estimates.

**Theorem 1.1 (Optimal weighted cycle-union variance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.optimal_cycle_union_area_variance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.optimal_cycle_union_area_variance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For positive weights in [c, 1], deviations at most d inside a band and D outside, and outside fraction at most 1/r, the weighted squared deviation is at most d² + (D² − d²)/(1 + c(r − 1)) when 0 ≤ d ≤ D and r ≥ 1. The outside weight occupies at most 1/(1 + c(r − 1)) of the total. The explicit r-element model with one weight-one deviation D and r − 1 weight-c deviations d attains equality.

**Theorem 1.2 (Finite anchor and per-band capacity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.finite_and_card_fiber_le_of_eventually_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.finite_and_card_fiber_le_of_eventually_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Let q be the size of a finite anchor and q_j the number of its indices in band j. Suppose every nonempty finite superset of the anchor has positive cutoff amplitude, the stated weighted boost estimate holds on cuts with outside fraction at most 1/r, and K²(d² + D²/(rc)) ≤ δ²/4 for r ≥ 2. A finite in-band set of size at least max(1, q_j + (r − 1)(q − q_j)) pads the anchor to an admissible nonempty cut. The existing cycle-union variance theorem makes its amplitude nonpositive, a contradiction. Every band is therefore finite with cardinal at most the threshold minus one, and the index type is finite.

**Theorem 1.3 (Quantitative Hilbert-space dimension bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.finrank_le_of_eventually_positive_cycle_cuts`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.finrank_le_of_eventually_positive_cycle_cuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Under the finite-anchor cutoff assumptions, a Hilbert basis has finite cardinal. Summing the band capacities gives finrank ℂ H ≤ q(1 + (m − 1)(r − 1)) − m when q > 0, where m is the number of bands. An empty anchor forces finrank ℂ H = 0. The estimate includes the equality boundary of the small-variance condition and supplies a quantitative repair of Eq. 5.38.

**Theorem 1.4 (Exact one-sided joint-cut tail modulus).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.disjoint_joint_cut_one_sided_tail_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.disjoint_joint_cut_one_sided_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For nonnegative w and a finite probability distribution v with event mass p in (0, 1), each finite set K outside a completed set of fibers J gives signed sums ±p(1 − p)∑_{i∈K} w_i on the full event side or its complement. The absolute signed sum over arbitrary finite pairs outside J is bounded by p(1 − p) times the weight of their distinct first coordinates. The estimate follows by bounding the positive and negative contributions separately and applies to the cutoff in Eq. 5.45.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.disjoint_joint_cut_one_sided_tail_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.finite_and_card_fiber_le_of_eventually_positive`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.finrank_le_of_eventually_positive_cycle_cuts`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound.optimal_cycle_union_area_variance_bound`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary](ClosedTraceFinitenessBoundary.md)
