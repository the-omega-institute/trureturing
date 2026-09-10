# PartitionLogCocycle

## Abstract

Branch-correct normalized logarithms of actual finite-grid partitions.

**Definition 1.1 (increment).**

Lean statement: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment`

*Formalization.* `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual insertion factor, inverse to the marked vacancy when the partitions are nonzero. A missing vertex gives one on the established activity tube.

**Theorem 1.2 (grid partition differentiable).**

Lean statement: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.grid_partition_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.grid_partition_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite independent-configuration sum is an entire function.

**Theorem 1.3 (grid partition zero).**

Lean statement: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.grid_partition_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.grid_partition_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty configuration is the only nonzero contribution at activity zero.

**Theorem 1.4 (increment halfplane).**

Lean statement: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_halfplane`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_halfplane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The origin half-plane estimate transports to every marked vertex, including an absent vertex. No direct bound on the argument of the whole partition is used.

**Theorem 1.5 (increment ne zero).**

Lean statement: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each actual insertion factor is nonzero on the common tube.

**Theorem 1.6 (increment log im).**

Lean statement: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_log_im`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_log_im` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity of the real part bounds the imaginary part of the principal log. This bound is what makes two successive log increments branch-compatible.

**Theorem 1.7 (increment square).**

Lean statement: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_square`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two ordered deletion steps have the same actual product after swapping vertices. All denominator nonvanishing facts are supplied by the concrete grid theorem.

**Theorem 1.8 (increment log square).**

Lean statement: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_log_square`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_log_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact additive flatness on every deletion square. The equality is in ℂ, not merely modulo 2*pi*i; the individual right-half-plane bounds prove the branch choice.

**Definition 1.9 (response).**

Lean statement: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.response`

*Formalization.* `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.response` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The logarithmic derivative of the actual partition. It is finite at z=0 and uses no logarithm branch in its definition.

**Theorem 1.10 (increment log hasDerivAt).**

Lean statement: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_log_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_log_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiate the actual local principal logarithm. Its derivative is the exact difference of two actual logarithmic derivatives, enabling telescoping.

**Theorem 1.11 (grid partition norm upper).**

Lean statement: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.grid_partition_norm_upper`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.grid_partition_norm_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Direct configuration comparison gives a volume upper bound on the entire complex plane. This does not use the recursion or the zero-free theorem.

## References

- Truth anchor: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.grid_partition_differentiable`
- Truth anchor: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.grid_partition_norm_upper`
- Truth anchor: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.grid_partition_zero`
- Truth anchor: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment`
- Truth anchor: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_halfplane`
- Truth anchor: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_log_hasDerivAt`
- Truth anchor: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_log_im`
- Truth anchor: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_log_square`
- Truth anchor: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_ne_zero`
- Truth anchor: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.increment_square`
- Truth anchor: `D5/S3/HardCoreHolomorphic/PartitionLogCocycle.response`
- Dependency: [D5/S3/HardCoreHolomorphic/FiniteGridZeroFree](FiniteGridZeroFree.md)
