# Positive pair-sum threshold for zeta collisions

## Abstract

A fixed positive upper threshold for the pair sum is sufficient at critical resolution.

The inclusive cutoff counts each positive ordinate with analytic multiplicity. Write N(Y) for this count and S_Y(t) for its phase sum. In G_Y(t), sum over all ordered pairs of retained ordinate labels, including the diagonal. The summand is the product of the two analytic multiplicities times 4 cos(t (gamma-gamma'))/(4+(gamma-gamma')^2). To obtain G_Y(t) from the normalized Montgomery function, evaluate at alpha=t/log(Y) and multiply by Y log(Y)/(2 pi).

Let c=1/(2 pi). The premise P asserts that a constant kappa in (0,2 c^2/3) satisfies G_Y(t)<=kappa Y log(Y)^2 uniformly on every fixed band log(Y)<=|t|<=A log(Y) for all sufficiently large Y, for each fixed A>1.

**Theorem 1.1 (Transfer from the inclusive cutoff to harmonic weights).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalPairSumThreshold.harmonic_long_deficit_of_cutoff_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalPairSumThreshold.harmonic_long_deficit_of_cutoff_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume RH and a fixed positive fractional deficit of the multiplicity-weighted phase sum on every fixed logarithmic band. The normalized harmonic phase score has a deficit at least d/log(Y) with one d > 0 valid on every band for sufficiently large Y depending on the band. The harmonic coefficient per multiplicity is at least 1/(2Y), and the total harmonic mass is asymptotic to (c/2) log(Y)^2.

**Theorem 1.2 (Critical Gaussian collision limit under the positive threshold).**

$$\begin{aligned}RH \land P \land T_{n} \to \infty \land \frac{(\log(T_{n}))^{2}}{n} \to 0\\\land \frac{\varepsilon_{n}}{s_{n}} \to 0\\\land (\exists a>0, \exists n_{0}, \forall n\ge n_{0}, 0<\varepsilon_{n} \land a\le \varepsilon_{n} \cdot \log(T_{n}))\\\longrightarrow \lim_{n \to \infty} \frac{s_{n} \cdot E_{n}(\varepsilon_{n})}{\varepsilon_{n} \cdot \operatorname{W}\left(T_{n}\right)^{2 \cdot n}} = \frac{1}{\sqrt{\pi}}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalPairSumThreshold.harmonic_zeta_critical_collision_limit_of_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write W(T) for the total harmonic weight and E_n(r) for the original inclusive hard-collision mass. The scale s_n is sqrt(n P_2(T_n)/2), where P_2 is the second pair moment of the normalized weights. RH denotes the Riemann hypothesis.

The squared phase peak has exponential energy G_Y(t). A nonnegative profile with central value b and slope bound L lies above max(b-L|u|,0). For r=b/L the energy of this tent is L^2 (r^2-r+(1-exp(-2r))/2), and the tent attains that energy. Bounding the exponential by its minimum on the tent support gives b^3<=(3/2) exp(2/Y) Y N(Y) G_Y(t) with L=Y N(Y). The zero-mass cutoff has zero phase sum.

Since N(Y)/(Y log(Y)) tends to c, the strict threshold gives a fixed positive fractional deficit for |S_Y(t)|. The harmonic coefficient per multiplicity is at least 1/(2Y) throughout the inclusive cutoff. Monotonicity of the norm deficit under increasing weights and the harmonic mass asymptotic give a positive constant times 1/log(Y) as the normalized deficit.

The Landau estimate supplies the short-band deficit. Annulus decay and the relative Fejer tail then give the Gaussian constant at every fixed neighboring resolution, which yields the inclusive hard-band limit. The uniform upper bound on G_Y is an arithmetic premise.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalPairSumThreshold.harmonic_long_deficit_of_cutoff_deficit`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalPairSumThreshold.harmonic_zeta_critical_collision_limit_of_threshold`
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryWindow](../../../../../Analytic/Oscillation/MontgomeryWindow.md)
- Dependency: [D5/S3/Fourier/Concentration/ExponentialTentEnergy](../../../../../Fourier/Concentration/ExponentialTentEnergy.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/OmittedSpectrumCutoff](OmittedSpectrumCutoff.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicCollisionLimit](RHLogarithmicCollisionLimit.md)
- Dependency: [D5/S3/Weil/ZetaExplicit/LandauUniformCutoff](../../../../ZetaExplicit/LandauUniformCutoff.md)
