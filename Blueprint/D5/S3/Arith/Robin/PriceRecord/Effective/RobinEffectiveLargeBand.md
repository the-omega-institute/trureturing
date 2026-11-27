# Effective Robin inequality above 5040

## Abstract

The effective Robin inequality above 5040 follows when every actual zero occurrence lies on the critical line.

The proof applies the full prime-power ledger to the same integer and real cutoff supplied by the attained failure minimum. The tangent rows cover log height through 101. The five exact prime rosters cover real cutoffs from 100 through 10000. When every actual zero occurrence lies on the critical line, Abel summation and the weighted zero bound give the prime band a normalized surplus of at least 17692481023/192060000000 for z ≥ 10000.

**Theorem 1.1 (Strict reserve for large cutoffs).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.normalized_prime_band_large`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.normalized_prime_band_large` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every actual zero occurrence has real part 1/2, then for every real z ≥ 10000 the normalized prime-band surplus strictly exceeds the combined error and curvature budget (1 + 1/log z)/20 + 2/√z + (1 + 1/log z)/(8z√z).

**Theorem 1.2 (Positive Robin log margin).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.effective_robin_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.effective_robin_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every actual zero occurrence has real part 1/2, the Robin log margin of each natural number n > 5040 is strictly positive.

**Theorem 1.3 (Divisor-sum inequality on the zero line).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.effective_robin_of_line`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.effective_robin_of_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every actual zero occurrence has real part 1/2, then for every natural number n > 5040 the sum of its positive divisors is strictly less than exp(γ) · n · log(log(n)), where γ is Euler’s constant.

**Theorem 1.4 (Divisor-sum inequality under the Riemann hypothesis).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.effective_robin_of_rh`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.effective_robin_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Riemann hypothesis puts every actual zero occurrence on the critical line. It follows that for every natural number n > 5040 the sum of its positive divisors is strictly less than exp(γ) · n · log(log(n)).

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.effective_robin_margin`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.effective_robin_of_line`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.effective_robin_of_rh`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.normalized_prime_band_large`
- Dependency: [D5/S3/Arith/Robin/ActualRobinInterval](../../ActualRobinInterval.md)
- Dependency: [D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows](../../Finite/EffectiveRobinTangentRows.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeBandCertificates](EffectivePrimeBandCertificates.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel](RobinEffectiveAbel.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope](../../../../Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.md)
