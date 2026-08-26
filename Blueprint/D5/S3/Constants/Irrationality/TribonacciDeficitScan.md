# Tribonacci Deficit Scan

## Abstract

The implemented Tribonacci deficit uses the source-normalized Binet leading term on an exact triangular scan.

The implemented quantity assigns a canonical no-111 Tribonacci name to each natural number, evaluates the occupied digits with the frozen Binet leading coefficient, and defines the addition deficit as the two readings minus the reading of their sum. The normalization bridge identifies that value with the source's shifted Binet coefficient. Thus the deficit is computed from the Binet leading term for this implemented definition.

The finite domain used by the certificate is exactly the triangular scan 1 <= v1 <= v2 <= 200, containing 20,100 pairs. Exact cubic arithmetic keeps the scan symbolic, and a nonzero quadratic coordinate is a certificate of genuine real nonintegrality at the Tribonacci root.

**Theorem 1.1 (The Binet face has the source normalization).**

$$\mathit{tribonacciBinetNameValue} = \mathit{sourceNormalizedBinetValue}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciDeficitScan.tribonacciBinetNameValue_eq_source_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality uses the existing exact normalization bridge; it does not reconstruct the coefficient from a decimal approximation.

**Theorem 1.2 (The triangular scan has 20,100 pairs).**

$$\operatorname{card}\left(\mathit{tribonacciScanPairs}\right) = 20100$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciDeficitScan.tribonacci_scan_pair_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the cardinality of the fixed window 1 <= v1 <= v2 <= 200, not the size of an unrestricted or externally supplied scan.

**Theorem 1.3 (A quadratic coordinate certifies nonintegrality).**

$$\operatorname{quadratic}\left(x\right) \ne 0 \Rightarrow \left(\neg \operatorname{tribonacciCodeValue}\left(x\right) \in \mathbb{Z}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciDeficitScan.tribonacci_code_value_not_integer_of_quadratic_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof rules out an integer value at the real Tribonacci root rather than treating a symbolic coordinate test as sufficient by itself.

## References

- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciDeficitScan.tribonacciBinetNameValue_eq_source_normalization`
- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciDeficitScan.tribonacci_code_value_not_integer_of_quadratic_ne_zero`
- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciDeficitScan.tribonacci_scan_pair_count`
- Dependency: [D5/S0/Tower/Champions/CodingFingerprint](../../../S0/Tower/Champions/CodingFingerprint.md)
- Dependency: [D5/S0/Tower/Champions/DecimalBounds](../../../S0/Tower/Champions/DecimalBounds.md)
- Dependency: [D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator](../../../S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator.md)
- Dependency: [D5/S0/Tower/Tribonacci/Representation](../../../S0/Tower/Tribonacci/Representation.md)
- Dependency: [D5/S3/Constants/Irrationality/TribonacciIrrationality](TribonacciIrrationality.md)
