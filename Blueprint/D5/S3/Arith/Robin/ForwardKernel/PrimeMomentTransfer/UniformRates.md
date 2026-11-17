# Uniform transfer rates

## Abstract

The error rates in cubic and fourth moment transfer vanish uniformly over polynomial length bands.

**Theorem 1.1 (A positive transfer exponent).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.transfer_epsilon_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.transfer_epsilon_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every beta less than one quarter, there is a positive epsilon less than one half minus twice beta.

**Theorem 1.2 (The sampling square-root rate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.sqrt_rate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.sqrt_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive alpha and positive tolerance delta, sqrt(log(N)/H) is at most delta for all sufficiently large real N, uniformly over every real H at least N to the power alpha.

**Theorem 1.3 (The cubic arithmetic rate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.arithmetic_rate_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.arithmetic_rate_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If beta and epsilon are positive and epsilon is less than one half minus three halves times beta, then N to the power minus one half plus epsilon, times H to the power three halves, times log(N) to the power minus three halves, tends to zero uniformly for real H between one and N to the power beta.

**Theorem 1.4 (The fourth arithmetic rate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.arithmetic_rate_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.arithmetic_rate_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive epsilon less than one half minus twice beta, N to the power minus one half plus epsilon, times H squared, times log(N) to the power minus two, tends to zero uniformly for real H between zero and N to the power beta.

**Theorem 1.5 (The inverse logarithm rate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.inverse_log_rate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.inverse_log_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive delta, the reciprocal of log(N) is at most delta for all sufficiently large real N.

**Theorem 1.6 (An antitone error modulus).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.antitone_modulus_rate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.antitone_modulus_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If eta is antitone on the real numbers at least two and tends to zero at infinity, then for positive alpha and delta, eta(H) is at most both eta(N to the power alpha) and delta, uniformly for H at least N to the power alpha once N is sufficiently large.

**Theorem 1.7 (The cell quadrature rate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.cell_rate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.cell_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative beta less than one half and every natural k at most four, (H log(N)) to the power k/2 divided by N tends to zero uniformly for real H between one and N to the power beta.

**Theorem 1.8 (The eventual length window).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.range_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.range_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive alpha and M and beta less than one, all sufficiently large real N satisfy N at least two and log(N) at least one. Every real H between N to the power alpha and N to the power beta then satisfies H at least two, H at most N, and M times H at most N.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.antitone_modulus_rate`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.arithmetic_rate_four`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.arithmetic_rate_three`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.cell_rate`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.inverse_log_rate`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.range_geometry`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.sqrt_rate`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.transfer_epsilon_exists`
