# Quartic positivity at the Wu endpoint

## Abstract

A quartic variance bound for the four prefix averages of the Wu endpoint convolution.

At the tracial three-to-four endpoint, the classical convolution majorizes the ordered spectrum of the signed two-mode output. For a nonzero positive semidefinite input, the prefix reduction for maximizing the sum of t⁴ − κt³ over the majorization polytope uses the four tail averages, with κ equal to the ratio of the third and second input moments.

**Definition 1.1 (Normalized spectral moment).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix.spectralMoment`

*Formalization.* `D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix.spectralMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The moment of order j of a real four-vector is the sum of its jth powers divided by four.

**Definition 1.2 (Prefix average).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix.endpointPrefixAverage`

*Formalization.* `D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix.endpointPrefixAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep the first k entries for k from zero to three and replace every remaining entry by the mean of that tail.

**Theorem 1.3 (Quartic bound for every prefix average).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix.endpoint_quartic_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix.endpoint_quartic_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let x be any nonnegative nonincreasing real four-vector. Let y be any of the four prefix averages of the classical two-bit endpoint convolution of x with damping square root of two thirds. The product of the third moments of x and y minus the product of the second moment of x and fourth moment of y is at least one fifth of the square of the first moment of x times the square of its variance.

For the constant prefix average, the estimate follows from Cauchy–Schwarz and nonnegativity of the variance. In the other three cases, expand in the smallest entry and the adjacent gaps of x. Splitting on the order of the two outer gaps gives polynomial expansions with nonnegative coefficients and weighted squares.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix.endpointPrefixAverage`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix.endpoint_quartic_prefix`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix.spectralMoment`
- Dependency: [D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization](WuEndpointPrefixMajorization.md)
