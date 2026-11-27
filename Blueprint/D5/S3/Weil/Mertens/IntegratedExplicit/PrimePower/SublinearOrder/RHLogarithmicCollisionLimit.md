# Collision limit at logarithmic observation times

## Abstract

Gaussian hard collisions for the harmonic zeta spectrum under a uniform ordinate-sum bound.

Use a positive zeta cutoff T with analytic multiplicities. The harmonic weights are a(gamma)=m(gamma) gamma/(1/4+gamma^2), with total W(T). Their normalized second pair moment is P_2(T). For each degree n, E_n(r) counts all pairs of degree-n occupation vectors whose frequency difference has magnitude at most r, with the product of their original harmonic multinomial weights.

**Theorem 1.1 (Gaussian hard-collision limit for the harmonic cutoff spectrum).**

$$\lim_{n \to \infty} \frac{s_{n} \cdot E_{n}(\varepsilon_{n})}{\varepsilon_{n} \cdot \operatorname{W}\left(T_{n}\right)^{2 \cdot n}} = \frac{1}{\sqrt{\pi}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicCollisionLimit.harmonic_zeta_collision_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume RH and the uniform multiplicity-weighted ordinate-sum envelope of the logarithmic-time deficit theorem for some positive constant C. For T_n tending to infinity, assume log(T_n)^2/n tends to zero. Put s_n=sqrt(n P_2(T_n)/2). Assume the resolutions epsilon_n are eventually positive, epsilon_n/s_n tends to zero, and epsilon_n log(T_n) tends to infinity. The displayed normalization of the inclusive hard-collision mass tends to the stated value.

Separate the symmetric Fourier integral at 1/T_n. The fourth moment bound P_4(T)<=T^2 P_2(T) makes s_n/T_n an admissible scaled radius for the central Gaussian theorem. The second moment lower bound makes that radius tend to infinity.

On 1/T_n<=|t|<=log(T_n), the reciprocal-time, periodic-phase and Landau bounds give a common deficit of at least 1/(1048576 log(T_n)) for the normalized score. After the score is raised to degree 2n, the annulus bound is controlled by T_n sqrt(n) log(T_n) times an exponential in -n/log(T_n). The growth separation absorbs the polynomial and cutoff factors, so this normalized contribution tends to zero.

Relative Fejer truncation controls the part beyond log(T_n). The resulting Fejer limit holds for every fixed positive multiple of epsilon_n, so the normalized ramp profile has limit x^2/(2 sqrt(pi)) near x=1. Its derivative gives the inclusive hard-band limit by the two-sided secant theorem. The multinomial normalization divides the original pair weights by W(T_n)^(2n).

The actual_cutoff_landau_envelope theorem supplies the assumed envelope under RH. For bounded epsilon_n log(T_n), the relative tail estimate used here does not tend to zero.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicCollisionLimit.harmonic_zeta_collision_limit`
- Dependency: [D5/S3/Fourier/Asymptotics/MovingFejerGaussianPrincipal](../../../../../Fourier/Asymptotics/MovingFejerGaussianPrincipal.md)
- Dependency: [D5/S3/Fourier/Concentration/FejerCollisionLimit](../../../../../Fourier/Concentration/FejerCollisionLimit.md)
- Dependency: [D5/S3/Fourier/Concentration/FejerRelativeLocalization](../../../../../Fourier/Concentration/FejerRelativeLocalization.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicAnnulusDecay](RHLogarithmicAnnulusDecay.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHPeriodicPhaseCoverage](RHPeriodicPhaseCoverage.md)
