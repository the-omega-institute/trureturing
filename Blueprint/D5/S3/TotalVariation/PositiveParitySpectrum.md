# Realizing a positive parity spectrum

## Abstract

Half-space moment products decide affine independent-bit realizability when all sign moments are positive.

**Theorem 1.1 (The half-space product criterion).**

Lean statement: `D5/S3/TotalVariation/PositiveParitySpectrum.positive_moment_realizability`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/PositiveParitySpectrum.positive_moment_realizability` (`✓ std3`). ∎

*Citation.* Muhammad Ardiyansyah, Dimitra Kosta, and Kaie Kubjas (2021). *The model-specific Markov embedding problem for symmetric group-based models*. DOI: [10.1007/s00285-021-01656-5](https://doi.org/10.1007/s00285-021-01656-5).

*Commentary.*

Let A be a finite additive commutative group with x+x=0 for all x. Let p be a real mass function whose total mass is one and whose sign moments are all strictly positive. For every nonzero a in A, compare the product of the moments over characters taking value -1 at a to the product over characters taking value +1 there. The former must be at most the latter.

The inequalities are necessary if p is an affine independent-bit law for any finite input type, any column map into A, any offset, and any input bias factors in the closed interval from -1 to 1. If the inequalities hold, there is a representation with offset zero and the identity column map on A. Every bias factor lies in (0,1]. A bit on the zero column contributes zero regardless of its value.

Take logarithms of the positive moments. Fourier inversion gives a logarithmic bias at each column. The half-space inequalities make each nonzero-column logarithmic bias nonpositive, so exponentiating gives a valid bias factor. Moment inversion identifies the reconstructed mass function with p. This is the elementary binary-group case of the symmetric model embedding criterion.

## References

- Truth anchor: `D5/S3/TotalVariation/PositiveParitySpectrum.positive_moment_realizability`
- Dependency: [D5/S3/TotalVariation/GroupedParityBias](GroupedParityBias.md)
