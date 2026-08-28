# Tribonacci Deficit Scan Certificate

## Abstract

The triangular Tribonacci scan has a strict bound, an exact nonintegral count, and an exact eight-point cubic spectrum.

On the certified triangular scan, the real deficit agrees with its exact layer-ten cubic code. The nonintegral filter has 8,934 members out of 20,100; membership proves genuine real nonintegrality, while every pair in the scan complement has an integral, in fact zero, deficit. The exact ratio 8934/20100 lies in the interval from 0.4435 inclusive to 0.4445 exclusive, so it rounds to 44.4 percent.

For the same certified pairs, every deficit has absolute value strictly less than 955/1000. Their exact cubic-code image is exactly the listed eight-point spectrum, including zero, so the scan values form this finite discrete spectrum.

The strict bound and the rounded percentage are proved only for the certified triangular scan 1 <= v1 <= v2 <= 200; they are not unrestricted claims about an unspecified source scan. Outside that scan, those two source claims remain unestablished.

The certificate does not establish that this spectrum is the trace lattice of the complex conjugate pair. The exact-spectrum theorem is a finite image statement and supplies no conjugate-pair trace map or lattice identification.

**Theorem 1.1 (The real deficit agrees with the exact code).**

$$\operatorname{tribonacciDeficit}\left(\mathit{pair}\right) = \operatorname{tribonacciCodeValue}\left(\operatorname{tribonacciDeficitCodeAt10}\left(\mathit{pair}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_scan_deficit_eq_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This bridge is restricted to pairs in the certified scan and connects the implemented Binet deficit to the finite exact computation.

**Theorem 1.2 (The nonintegral filter has 8,934 members).**

$$\operatorname{card}\left(\mathit{tribonacciNonintegralScanPairs}\right) = 8934$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_nonintegral_scan_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Four kernel-checked row blocks sum to the exact count for the fixed triangular window.

**Theorem 1.3 (Filter membership is genuine nonintegrality).**

$$\mathit{pair} \in \mathit{tribonacciNonintegralScanPairs} \Rightarrow \left(\neg \operatorname{tribonacciDeficit}\left(\mathit{pair}\right) \in \mathbb{Z}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_nonintegral_of_mem_scan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero exact quadratic coordinate is carried through the code-value bridge to rule out equality with every integer.

**Theorem 1.4 (The scan complement is integral).**

$$\left(\mathit{pair} \in \mathit{tribonacciScanPairs} \land \left(\neg \mathit{pair} \in \mathit{tribonacciNonintegralScanPairs}\right)\right) \Rightarrow \operatorname{tribonacciDeficit}\left(\mathit{pair}\right) \in \mathbb{Z}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_integral_of_mem_scan_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On this finite spectrum, a zero quadratic coordinate forces the whole code to be zero, so the complement contributes no additional nonintegral deficits.

**Theorem 1.5 (The exact ratio rounds to 44.4 percent).**

$$\frac{4435}{10000} \le \frac{8934}{20100} \land \frac{8934}{20100} < \frac{4445}{10000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_nonintegral_scan_percentage_rounds_to_44_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem proves the rational half-open rounding interval directly; it does not rely on floating-point evaluation.

**Theorem 1.6 (The code image is the eight-point spectrum).**

$$\operatorname{image}\left(\mathit{tribonacciDeficitCodeAt10}, \mathit{tribonacciScanPairs}\right) = \mathit{tribonacciScanSpectrum}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_scan_spectrum_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inclusion is certified across all four row blocks, and explicit scan witnesses show that every listed cubic code occurs.

**Theorem 1.7 (Every certified deficit obeys the strict bound).**

$$\mathit{pair} \in \mathit{tribonacciScanPairs} \Rightarrow \left|\operatorname{tribonacciDeficit}\left(\mathit{pair}\right)\right| < \frac{955}{1000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_deficit_scan_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict inequality is proved for each spectral code and transferred to every pair in the certified triangular scan.

## References

- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_deficit_scan_bound`
- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_integral_of_mem_scan_complement`
- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_nonintegral_of_mem_scan`
- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_nonintegral_scan_count`
- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_nonintegral_scan_percentage_rounds_to_44_4`
- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_scan_deficit_eq_code`
- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.tribonacci_scan_spectrum_exact`
- Dependency: [D5/S3/Constants/Irrationality/TribonacciDeficitScan](TribonacciDeficitScan.md)
