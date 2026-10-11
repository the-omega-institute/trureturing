# Full Bispectrum Stability

## Abstract

Calibrated full bispectra determine a unique nearby cyclic translation with an explicit error bound.

**Theorem 1.1 (Recovery from raw complex bispectrum errors).**

Lean statement: `D5/S3/Fourier/FullBispectrumStability.full_bispectrum_stability`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/FullBispectrumStability.full_bispectrum_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f and g be complex signals on ZMod N, with N positive. Write F and J for their unnormalized negative-exponent discrete Fourier transforms. Assume their zero-frequency coefficients coincide, every source amplitude |F(k)| is at least m>0, and every full bispectrum entry J(k)J(l)conj(J(k+l)) differs from F(k)F(l)conj(F(k+l)) by at most epsilon, where 0<=epsilon<=m^3/4.

There is a cyclic translation t for which the counting-measure squared signal error sum_x |g(x)-f(x-t)|^2 is at most R^2, where R=2 epsilon/m^2. Every Fourier coefficient error |J(k)-exp(-2 pi i k t/N)F(k)| is at most R. Every translation satisfying the squared signal error bound equals t. The group of order one and both error endpoints are included.

The calibrated zero-frequency slice first bounds the squared amplitude error and rules out zeros in J. Normalize F and J to unit phases and let r be their relative phase. With weights p(k)=|F(k)||J(k)|, the raw bispectrum errors bound p(k)p(l)p(k+l)|r(k)r(l)-r(k+l)|^2 by epsilon^2, and each p(k) is at least 3m^2/4.

Character orthogonality and Parseval express the cubic phase correlation as a weighted average of Fourier coefficients. One genuine finite character has a coefficient of norm at least 8/9. Averaging the multiplicative defect against this character and using the lower bounds for the other two weights yields p(k)|r(k)-chi(k)|^2<=9 epsilon^2/(4m^4). The radial identity then bounds the coefficient error squared by 13 epsilon^2/(4m^4), below R^2.

Counting Parseval transfers the coefficient bound to signal error without a factor of sqrt(N). Distinct translations have squared distance at least 2m^2, so two translations cannot both lie in the radius-R error ball.

A noisy family occurs already for N=2. Set F=(1,a) and J=(1,a+eta), with 0<a<=1 and eta>0, and take their inverse DFT signals. Their zero-frequency coefficients coincide, the source minimum is a, and their signals differ. The bispectrum difference is zero at (0,0) and equals the real number 2a eta+eta^2 at each other pair. Thus the theorem applies whenever 2a eta+eta^2<=a^3/4, despite genuine amplitude noise.

The estimate uses all pairs of frequencies; it does not assert this bound from a generator row alone. Separate observation error and reconstruction residual may be added by the triangle inequality before applying the theorem. This is a stability statement for any reconstruction satisfying the hypotheses, and supplies no guarantee that an optimization algorithm attains that residual.

For a wheel signal with an established minimum Fourier amplitude m_W and exact calibrated mass, two residual bounds of eta give R=4 eta/m_W^2 when eta<=m_W^3/8. A nontrivial translation orbit needs an additional phase anchor to identify its absolute origin. The arithmetic amplitude bounds, acquisition costs, prime-correlation errors, and analytic claims about primes are separate inputs.

## References

- Truth anchor: `D5/S3/Fourier/FullBispectrumStability.full_bispectrum_stability`
- Dependency: [D5/S3/Fourier/FinitePoisson](FinitePoisson.md)
