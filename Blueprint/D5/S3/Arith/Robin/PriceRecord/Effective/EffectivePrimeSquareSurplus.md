# Exact prime-square surplus in the actual Robin ledger

## Abstract

An exact prime-square band reserve from the complete actual Robin ledger.

For a real cutoff z and a positive integer n whose prime support is exactly the primes at most z, the complete signed prime-power ledger is retained. Every occupied prime p with p^2>2z contributes a strict explicit weight (p-2)/(2(p-1)p^2), including the whole shifted Euler tail and every actual valuation.

The finite band is the filtered prime set p<=floor(z) and 2z<p^2. The normalized band multiplies its exact rational weights by sqrt(z) log z. The reserve needed for the weighted zero term and the log-log curvature is stated with the exact constants 1/20, 2 and 1/8.

**Definition 1.1 (Prime-band weight).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.primeBandWeight`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.primeBandWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact weight assigned to a prime p is (p-2)/(2(p-1)p^2).

**Definition 1.2 (Actual prime band).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.primeBand`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.primeBand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The band contains exactly the primes p at most floor(z) with 2z<p^2.

**Definition 1.3 (Complete arithmetic surplus).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.arithmeticSurplus`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.arithmeticSurplus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the complete tail plus the exact log(n)-psi(z) inventory divided by z log z, less the full prime-power residual.

**Definition 1.4 (Square-root logarithmic normalization).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.D`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalization is sqrt(z) log z.

**Definition 1.5 (Normalized prime band).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.normalizedPrimeBand`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.normalizedPrimeBand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized band is D(z) times the finite sum of prime-band weights.

**Definition 1.6 (Required analytic reserve).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.neededReserve`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.neededReserve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The required reserve is (1/20)(1+1/log z)+2/sqrt z+(1+1/log z)/(8z sqrt z).

**Theorem 1.7 (Strict local prime-square surplus).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.prime_contribution_sqrt_two`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.prime_contribution_sqrt_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For z>=4, p<=z prime, p^2>2z and positive actual valuation, the exact prime-band weight is strictly below the complete local prime contribution.

**Theorem 1.8 (Band reserve below the full ledger).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.prime_band_le_full_surplus`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.prime_band_le_full_surplus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the strict local inequalities over the actual band and retaining nonnegative contributions from every other supported prime gives the band sum at most the complete arithmetic surplus.

**Theorem 1.9 (Effective Robin margin reduction).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.robin_margin_of_effective_band`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.robin_margin_of_effective_band` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite positive margin through log height 101, an exact prime-band reserve for every cutoff z>=100, and the weighted-tail lower bound together imply a positive original Robin log margin for every n>5040.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.D`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.arithmeticSurplus`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.neededReserve`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.normalizedPrimeBand`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.primeBand`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.primeBandWeight`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.prime_band_le_full_surplus`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.prime_contribution_sqrt_two`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.robin_margin_of_effective_band`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/CompleteSignedLedger](../CompleteSignedLedger.md)
