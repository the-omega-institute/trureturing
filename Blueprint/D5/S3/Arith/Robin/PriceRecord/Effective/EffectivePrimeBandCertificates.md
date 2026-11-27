# Finite exact prime-band certificates

## Abstract

Exact rational prime-band certificates cover every real cutoff from 100 through 10000.

Five closed intervals cover 100<=z<=10000. Each interval uses a finite roster of actual primes p<=L with p^2>2U, a certified square-root lower bound r, and a rational lower bound ell for log L.

The certificate keeps both real endpoints and the upper prime-band endpoint. All comparisons use exact rational logarithm enclosures and the native prime-band weight from EffectivePrimeSquareSurplus.

**Theorem 1.1 (Single interval certificate).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeBandCertificates.interval_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeBandCertificates.interval_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A roster satisfying the exact prime, endpoint, root and logarithm hypotheses proves neededReserve z < normalizedPrimeBand z throughout the closed interval [L,U].

**Theorem 1.2 (Finite cutoff coverage).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeBandCertificates.normalized_prime_band_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeBandCertificates.normalized_prime_band_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five literal rosters certify neededReserve z < normalizedPrimeBand z for every real z with 100<=z<=10000.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeBandCertificates.interval_certificate`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeBandCertificates.normalized_prime_band_finite`
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](../../../GoldenResource/RobinRationalBasis.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus](EffectivePrimeSquareSurplus.md)
