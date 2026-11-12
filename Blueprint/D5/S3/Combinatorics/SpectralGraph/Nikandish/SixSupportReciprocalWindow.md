# Strict reciprocal windows for the complete residual spectrum

## Abstract

The full endpoint-one reciprocal window and its necessary integer-spectrum test.

**Theorem 1.1 (Three separated positive roots).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportReciprocalWindow.three_reciprocals`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportReciprocalWindow.three_reciprocals` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every positive threshold s and all three real roots strictly above it, their reciprocal sum is positive and strictly less than 2/s+1/(T-2s). The proof allows repeated roots and consumes two exact pairwise strict inequalities.

**Theorem 1.2 (The full minimum-four endpoint-one window).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportReciprocalWindow.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportReciprocalWindow.result` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every ordered real 4<=a<=b<=c on h(1)=0, the actual residual quartic factors into one root mu in (a,min(c,a+b)) and three roots above s=a+b+c. With its exact coefficients N and D and R=2/s+1/(A-min(c,a+b)-2s), the proof establishes D-NR>0 before inversion and N/D<mu<N/(D-NR). No integral splitting, selected exponent family or supplied root oracle is assumed.

**Theorem 1.3 (Necessary integer-spectrum candidates).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportReciprocalWindow.integer_candidates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportReciprocalWindow.integer_candidates` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every ordered integer minimum-four endpoint-one triple, if all real residual roots are integers, there is a positive divisor d of N with F(d)=0 in the strict intersection of both spectral and reciprocal windows. All three other integer roots are at least s+1, and their full factorization is retained. A surviving divisor is not a sufficient integer-spectrum test and does not bound the unbounded exponent domain. The real b=2a width-limit and all reported control-candidate/congruence data remain separate source obligations; this theorem does not certify those calculations.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportReciprocalWindow.integer_candidates`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportReciprocalWindow.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportReciprocalWindow.three_reciprocals`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneArithmetic](SixSupportEndpointOneArithmetic.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportMiddleSpectrum](SixSupportMiddleSpectrum.md)
