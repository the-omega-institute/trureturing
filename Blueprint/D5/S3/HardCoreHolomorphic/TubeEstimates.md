# TubeEstimates

## Abstract

Explicit holomorphic hard-core coordinates and uniform complex neighborhoods.

**Definition 1.1 (delta).**

Lean statement: `D5/S3/HardCoreHolomorphic/TubeEstimates.delta`

*Formalization.* `D5/S3/HardCoreHolomorphic/TubeEstimates.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One width for every message type. It is deliberately conservative.

**Definition 1.2 (epsilon).**

Lean statement: `D5/S3/HardCoreHolomorphic/TubeEstimates.epsilon`

*Formalization.* `D5/S3/HardCoreHolomorphic/TubeEstimates.epsilon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One activity width for every finite domain and every pruning pattern.

**Theorem 1.3 (width arithmetic).**

Lean statement: `D5/S3/HardCoreHolomorphic/TubeEstimates.width_arithmetic`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/TubeEstimates.width_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact numerical margins used below.

**Theorem 1.4 (normalized inverse bound).**

Lean statement: `D5/S3/HardCoreHolomorphic/TubeEstimates.normalized_inverse_bound`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/TubeEstimates.normalized_inverse_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pole-free normalized Mobius increment controls the inverse coordinate.

**Theorem 1.5 (inverse tube).**

Lean statement: `D5/S3/HardCoreHolomorphic/TubeEstimates.inverse_tube`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/TubeEstimates.inverse_tube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every inverse chart is pole-free and stays close to its real interval. All three coefficient bounds are concrete numerical requirements, later checked on the actual Lean-owned coefficient table.

**Theorem 1.6 (product four bound).**

Lean statement: `D5/S3/HardCoreHolomorphic/TubeEstimates.product_four_bound`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/TubeEstimates.product_four_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One finite-product estimate covers three-child rows and the four-child root.

**Theorem 1.7 (quotient difference).**

Lean statement: `D5/S3/HardCoreHolomorphic/TubeEstimates.quotient_difference`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/TubeEstimates.quotient_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stable division, with the two concrete denominator floors used for the log argument.

## References

- Truth anchor: `D5/S3/HardCoreHolomorphic/TubeEstimates.delta`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TubeEstimates.epsilon`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TubeEstimates.inverse_tube`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TubeEstimates.normalized_inverse_bound`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TubeEstimates.product_four_bound`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TubeEstimates.quotient_difference`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TubeEstimates.width_arithmetic`
- Dependency: [D5/S3/HardCoreHolomorphic/TypedJacobian](TypedJacobian.md)
