# Joint Fourier Moments on the Cyclic Group of Order Four

## Abstract

Two squared Fourier magnitudes of a probability weight on the cyclic group of order four have an exact joint range.

A probability weight w on the cyclic group of order four assigns nonnegative real masses summing to one to the four residues. Use the unnormalized discrete Fourier transform. A pair (u,v) is attainable if a common weight has squared Fourier magnitudes u at frequency one and v at frequency two.

**Theorem 1.1 (The exact joint range of the first two squared magnitudes).**

$$\operatorname{Attainable}\left(u, v\right) \iff 0 \leq v \leq 1 \land 0 \leq u \leq \frac{1 + v}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FourthRootMomentRegion.dft_four_squared_region` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If e and o are the even and odd masses, the squared second magnitude is (e−o) squared. The two signed differences of masses within each parity can independently fill [−e,e] and [−o,o]. Their squared sum is at most e squared plus o squared, which is (1+v)/2. To attain any allowed pair, take e=(1+sqrt(v))/2 and o=(1−sqrt(v))/2. Vary both signed differences by the same fraction of their endpoint values.

For a natural number p at least two, let A be the maximum of the p-th power of the squared first magnitude among probability weights whose p-th power of the squared second magnitude vanishes. Let B be the maximum real nonnegative first Fourier coefficient among symmetric probability weights whose second Fourier coefficient vanishes.

**Theorem 1.2 (Different attained maxima for the powered moments and their relaxation).**

$$A = (\frac{1}{2})^{p} < \frac{1}{2} = B$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FourthRootMomentRegion.four_first_moment_maxima` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At v=0 the preceding interval ends at one half. Taking the p-th power gives the first attained maximum. In the relaxation, the vanishing second coefficient makes both parity masses one half. Symmetry makes the first coefficient the difference of the masses at zero and two. The weight (1/2,1/4,0,1/4) attains one half.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FourthRootMomentRegion.dft_four_squared_region`
- Truth anchor: `D5/S3/Fourier/Concentration/FourthRootMomentRegion.four_first_moment_maxima`
