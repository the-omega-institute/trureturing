# Offline-Zero Reflection-Quotient Coordinate

## Abstract

Reflection identifies the spectral quotient coordinate of an offline-zero parameter by an exact complex polynomial formula.

**Definition 1.1 (The reflection quotient gives the exact offline-zero coordinate).**

Lean statement: `D5/S3/Weil/ZetaLinear/OfflineZeroSpectralQuotient.offline_zero_spectral_quotient_coordinate`

*Formalization.* `D5/S3/Weil/ZetaLinear/OfflineZeroSpectralQuotient.offline_zero_spectral_quotient_coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate lambda(s) is defined as s times its existing functional reflection 1 - s, so the offline-zero parameter rho is shared with the preceding character construction.

Substituting rho = 1/2 + delta + i gamma gives real part 1/4 + gamma squared - delta squared and imaginary part -2 delta gamma.

The definition is realized concretely at delta = gamma = 1, where rho = 3/2 + i and lambda(rho) = 1/4 - 2i.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/OfflineZeroSpectralQuotient.offline_zero_spectral_quotient_coordinate`
- Dependency: [D5/S3/Weil/ZetaLinear/OfflineZeroCharacter](OfflineZeroCharacter.md)
