# Quartic majorization at the Wu endpoint

## Abstract

Quartic prefix majorization and the normalized trace bound for the signed two-mode Wu map.

**Definition 1.1 (Four-point spectrum).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.Spectrum4`

*Formalization.* `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.Spectrum4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A four-point spectrum is a real vector indexed by zero through three.

**Definition 1.2 (Quartic sum).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuarticSum`

*Formalization.* `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuarticSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real coefficient κ, sum t⁴ − κt³ over the four entries t of the spectrum.

**Theorem 1.3 (Comparison with a prefix average).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuartic_le_some_prefixAverage`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuartic_le_some_prefixAverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let v and y be nonincreasing real four-vectors, with v nonnegative. Suppose y has the same total sum as v and each of its three proper prefix sums is at most the corresponding prefix sum of v. For every real κ, some prefix average of v has quartic sum at least that of y.

The majorization region is compact and invariant under permutations. Sort a maximizer and take its first slack prefix. The two entries straddling that prefix admit a small mass transfer in either direction. For a pair with mean m and half-difference d, stationarity and the quartic change under a transfer force d to vanish and m to be at most κ/2. Every later entry lies in the concavity interval from zero to κ/2, so Jensen’s inequality bounds the tail by its average. When all three prefixes are tight, the maximizer equals v.

**Definition 1.4 (Maximum over the four prefix averages).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuarticPrefixMax`

*Formalization.* `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuarticPrefixMax` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each prefix length from zero to three, keep that prefix of v and replace the remaining entries by their mean. Take the maximum of the four resulting quartic sums.

**Theorem 1.5 (Quartic sum bounded by the prefix maximum).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuartic_le_prefixMax`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuartic_le_prefixMax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same ordering, nonnegativity, prefix inequalities and total equality, the quartic sum of y for each real κ is bounded above by the maximum over the four prefix averages of v.

**Theorem 1.6 (Variance bound for majorized spectra).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.endpoint_quartic_floor_of_majorization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.endpoint_quartic_floor_of_majorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let x be a nonnegative nonincreasing real four-vector. Let y be nonincreasing, with the three proper prefix sums bounded by those of the classical Wu endpoint convolution of x and with the same total sum as that convolution. The product of the third moments of x and y minus the product of the second moment of x and fourth moment of y is at least one fifth of the squared first moment of x times its squared variance. Each moment is divided by four.

For a positive second moment, take κ to be the third input moment divided by the second and use the quartic bound for the maximizing prefix average. If the second moment vanishes, the input vector vanishes.

**Theorem 1.7 (Variance bound for the signed endpoint spectrum).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.A1_spectral_quartic_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.A1_spectral_quartic_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any positive semidefinite two-mode input X, take x to be its decreasing spectrum and y the decreasing spectrum of the signed Wu endpoint applied to X. The endpoint spectral majorization theorem supplies the prefix inequalities and total equality, so these spectra satisfy the same third- and fourth-moment variance bound.

**Definition 1.8 (Normalized trace moment).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.endpointTraceMoment`

*Formalization.* `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.endpointTraceMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural order k and each two-mode matrix, take the real part of the trace of its kth power, divided by four.

**Theorem 1.9 (Trace inequality at the tracial three-to-four endpoint).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.A1_quartic_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.A1_quartic_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive semidefinite two-mode matrix X, let Y be its image under the signed Wu endpoint. The product of the third normalized trace moments of X and Y minus the product of the second normalized trace moment of X and fourth normalized trace moment of Y is at least the squared first normalized trace moment of X times the squared normalized variance of X, divided by five.

Unitary diagonalization of a Hermitian matrix identifies its normalized trace moments with its normalized spectral moments. Apply this identity to X and Y to transfer the spectral bound to the actual matrix map.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.A1_quartic_floor`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.A1_spectral_quartic_floor`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.Spectrum4`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.endpointTraceMoment`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.endpoint_quartic_floor_of_majorization`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuarticPrefixMax`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuarticSum`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuartic_le_prefixMax`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.wuQuartic_le_some_prefixAverage`
- Dependency: [D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix](WuEndpointQuarticPrefix.md)
