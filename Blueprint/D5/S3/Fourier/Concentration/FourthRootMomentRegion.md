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

Fix a natural number p at least two. For a real weight w of total mass one, let u and v be the squared magnitudes of the unnormalized discrete Fourier transform of this same w at frequencies one and two, respectively. Write M(w) for the vector of Fourier coefficients at 0, 1, 2 and 3 of the singleton cyclic collision masses of the degree-p lattice sums. The lattice coordinate is its representative in {0,1,2,3}. With nonnegative w these masses form the law of the difference between two independent p-fold sums. Let A be the maximum of M(w) at frequency one over all nonnegative real weights w of total mass one for which M(w) at frequency two is zero. Let B be the maximum of the real numbers b at least zero for which a probability law on the four residues has Fourier coefficient vector (1,b,0,b).

**Theorem 1.2 (Different attained maxima for the powered moments and their relaxation).**

$$\operatorname{M}\left(w\right) = (1, u^{p}, v^{p}, u^{p}) \land A = (\frac{1}{2})^{p} < \frac{1}{2} = B$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FourthRootMomentRegion.four_first_moment_maxima` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The singleton cyclic collision formula and Fourier inversion recover each coefficient from the same weight. The first and third Fourier magnitudes agree because the weights are real. At v=0 the preceding interval ends at one half. Taking the p-th power gives the first attained maximum. In the relaxation, the vanishing second coefficient makes both parity masses one half. A real first coefficient forces the masses at one and three to agree, and the coefficient equals the difference of the masses at zero and two. The weight (1/2,1/4,0,1/4) attains one half.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FourthRootMomentRegion.dft_four_squared_region`
- Truth anchor: `D5/S3/Fourier/Concentration/FourthRootMomentRegion.four_first_moment_maxima`
- Dependency: [D5/S3/Fourier/Concentration/CyclicCollisionCertificate](CyclicCollisionCertificate.md)
- Dependency: [D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion](../../PrimeForms/Splitting/QuarticCharacterCompletion.md)
