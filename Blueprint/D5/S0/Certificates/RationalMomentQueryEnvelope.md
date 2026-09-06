# Certified omitted-query residual envelopes

## Abstract

A pointwise residual enclosure transfers a fixed moment compression to an entire certified query family. A zero weighted square residual implies exact reconstruction; cancellation of a signed mean does not.

**Definition 1.1 (Data-only affine residual envelope).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.QueryEnvelope`

*Formalization.* `D5/S0/Certificates/RationalMomentQueryEnvelope.QueryEnvelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Contains the affine predictor coefficients and rational lower and upper residual bounds.

**Definition 1.2 (Actual coefficient residual).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.queryResidual`

*Formalization.* `D5/S0/Certificates/RationalMomentQueryEnvelope.queryResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtracts the affine predictor from the actual query coefficient at each atom before averaging.

**Definition 1.3 (Center determined by retained moments).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.predictedMean`

*Formalization.* `D5/S0/Certificates/RationalMomentQueryEnvelope.predictedMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The center uses the retained feature means. It does not insert the unknown omitted-query expectation.

**Definition 1.4 (All-active-atom residual bounds).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.ValidQueryEnvelope`

*Formalization.* `D5/S0/Certificates/RationalMomentQueryEnvelope.ValidQueryEnvelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Requires the interval at each original nonzero atom, including atoms receiving larger mass after compression.

**Definition 1.5 (Exact finite envelope checker).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.checkQueryEnvelope`

*Formalization.* `D5/S0/Certificates/RationalMomentQueryEnvelope.checkQueryEnvelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decides the rational support-local inequalities. No numerical tolerance or estimated mean replaces them.

**Theorem 1.6 (Reflect envelope acceptance).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.checkQueryEnvelope_eq_true_iff`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentQueryEnvelope.checkQueryEnvelope_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Acceptance is equivalent to the coefficient inequalities needed in the expectation argument.

**Theorem 1.7 (Enclose the true expectation).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.query_interval_of_envelope`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentQueryEnvelope.query_interval_of_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative normalized weights transfer residual bounds to an interval around the retained-moment predictor.

**Theorem 1.8 (One interval for both laws).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_query_enclosures`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_query_enclosures` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Support containment and moment preservation put the original and compressed query values inside the same rational interval.

**Theorem 1.9 (Residual oscillation bounds query drift).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_query_error_bound`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_query_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute change is bounded by upper minus lower. A symmetric residual bound epsilon yields two epsilon.

**Theorem 1.10 (Keep one compression for the whole family).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_uniform_query_family`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_uniform_query_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compressed law and trace are fixed before the parameter is quantified. Each family envelope is checked on the same original support.

**Theorem 1.11 (Zero quadratic residual detects pointwise equality).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.residual_energy_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentQueryEnvelope.residual_energy_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative weights, zero weighted residual square is equivalent to residual zero at every active atom.

**Theorem 1.12 (Upgrade zero residual energy to exact query preservation).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_query_exact_of_zero_residual_energy`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_query_exact_of_zero_residual_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An exact zero energy gives a zero-width envelope and therefore preserves the query through every accepted compression of the specified features.

**Theorem 1.13 (Expose a missed probability query).**

Lean statement: `D5/S0/Certificates/RationalMomentQueryEnvelope.signed_residual_cancellation_counterexample`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentQueryEnvelope.signed_residual_cancellation_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A valid mean-preserving compression changes an omitted event from two thirds to zero despite its centered signed residual having zero original mean. The residual energy is two ninths.

## References

- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.QueryEnvelope`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.ValidQueryEnvelope`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.checkQueryEnvelope`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.checkQueryEnvelope_eq_true_iff`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_query_enclosures`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_query_error_bound`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_query_exact_of_zero_residual_energy`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.checked_uniform_query_family`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.predictedMean`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.queryResidual`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.query_interval_of_envelope`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.residual_energy_zero_iff`
- Truth anchor: `D5/S0/Certificates/RationalMomentQueryEnvelope.signed_residual_cancellation_counterexample`
- Dependency: [D5/S0/Certificates/RationalAffineMomentCompression](RationalAffineMomentCompression.md)
