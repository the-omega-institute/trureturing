# Exact Detection-Radius Certificate

## Abstract

The beta 0.51 and gamma 10^12 detection radius is exactly 10^1200.

**Theorem 1.1 (The specialized detection radius is exactly 10^1200).**

$$\frac{\log 10^{12}}{\frac{51}{100}-\frac{1}{2}} = 1200 \log 10 \land \exp (\frac{\log 10^{12}}{\frac{51}{100}-\frac{1}{2}}) = 10^{1200}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Detection/DetectionRadiusCertificate.detection_radius_ten_to_the_1200_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The atom gives the visibility-scale reading ln(gamma)/(beta - 1/2). For the exact inputs beta = 51/100 and gamma = 10^12, Lean proves that this logarithmic scale is 1200 log 10 and that its exponential is exactly 10^1200.

The denominator is checked separately as the nonzero rational 1/100. The proof uses pinned Mathlib's logarithm-of-a-power and exponential-of-logarithm identities; no decimal approximation is used.

The source writes the general visibility law with an approximation sign. This theorem certifies only its displayed beta = 0.51 and gamma = 10^12 arithmetic specialization exactly; it does not turn the surrounding approximate model into a universal exact law.

## References

- Truth anchor: `D5/S3/Zeros/Detection/DetectionRadiusCertificate.detection_radius_ten_to_the_1200_certificate`
