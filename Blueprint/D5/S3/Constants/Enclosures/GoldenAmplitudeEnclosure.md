# Golden Amplitude Enclosure

## Abstract

The exact golden amplitude satisfies the source's seven-digit enclosure.

**Theorem 1.1 (The golden amplitude lies in its certified decimal interval).**

$$\left|A_{h} - \frac{3408474}{10000000}\right| \le \frac{33}{100000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Enclosures/GoldenAmplitudeEnclosure.ah_seven_digit_enclosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The amplitude A_h is the canonical exact value (5 sqrt(5) - 3) / 24. Exact rational square comparisons place sqrt(5) between 2.236065936 and 2.236069104; linear arithmetic then proves that A_h differs from 0.3408474 by at most 0.00000033. No floating-point premise is used.

## References

- Truth anchor: `D5/S3/Constants/Enclosures/GoldenAmplitudeEnclosure.ah_seven_digit_enclosure`
