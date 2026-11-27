# Harmonic logarithmic annulus decay

## Abstract

A positive harmonic phase deficit forces decay of the normalized annulus integral.

Assume RH. Let H collect the hypotheses B>=1, c>0, T_n tending to infinity, eventual positivity of eta_n, and (log T_n)^2/n tending to zero. For all sufficiently large cutoff heights T, require normalized harmonic score magnitude at most 1-c/log(T) whenever 1/T<=|t|<=B log(T). Let I_n(R) integrate the Fejer kernel of parameter eta_n times the score magnitude to power 2n over the interval from -R to R. The scale s_n is the square root of n times the normalized second pair moment divided by two.

**Theorem 1.1 (Decay with an arbitrary positive deficit coefficient).**

$$H \longrightarrow \lim_{n \to \infty} \frac{s_{n}}{\varepsilon_{n}} (I_{n}(B \cdot \log(T_{n})) - I_{n}(\frac{1}{T_{n}})) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicAnnulusDecay.harmonic_multiple_log_annulus_limit_of_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the normalized score has a deficit at least c/log(T) for a fixed c>0 across the annulus, its 2n-th power is at most exp(-2cn/log(T)). The bound on the Fejer kernel cancels the normalization by the resolution. The annulus length is at most 2B log(T), and the phase variance bounds the scale by sqrt(n) T. These factors are dominated by the exponential when log(T)^2/n tends to zero.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicAnnulusDecay.harmonic_multiple_log_annulus_limit_of_deficit`
- Dependency: [D5/S3/Fourier/Asymptotics/MovingFejerGaussianPrincipal](../../../../../Fourier/Asymptotics/MovingFejerGaussianPrincipal.md)
- Dependency: [D5/S3/Fourier/Concentration/FejerCollisionLimit](../../../../../Fourier/Concentration/FejerCollisionLimit.md)
- Dependency: [D5/S3/Fourier/Concentration/FejerRelativeLocalization](../../../../../Fourier/Concentration/FejerRelativeLocalization.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLandauWindowTransfer](RHLandauWindowTransfer.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHPeriodicPhaseCoverage](RHPeriodicPhaseCoverage.md)
