# Complete Low-Height Weighted Spectral Mean

## Abstract

The full countable low-height mean is bounded by a decaying shell term and two explicit extensions.

The complete Gaussian mean identity reduces the physical integral on y > 1 to the all-index full-line mean and two signed extension integrals. This source bounds the divided cubic numerator after division by the actual nonzero resolvent denominator. For t = abs(Im(rho)) > 10, it obtains a core constant 2, then the paper's constant 20; neither imaginary sign is selected.

The h integral uses 3*(1+h) on [0,2], whose integral is 12. Thus core 20 gives the integrated coefficient 240, while core 2 gives 24 and absolute summability of the complex shell norms. The shell count gives 10000*exp(-100*m); multiplying by exp(17*m) yields the complete 2400000*exp(-83*m) term.

The positive extension keeps y in (0,1]. For the negative extension, the Gaussian tilt has center 12*m, variance 2*m and factor exp(-28*m). Its central second and fourth moments are 2*m and 12*m^2, giving the coefficient 384. These bounds apply to repeated zeros in the complete natural-index family.

For every real m >= 1 and gamma > 10, the additional scalar consequence is 24*m*(gamma+10)^2*(10000*exp(-100*m))*exp(17*m) <= m*(gamma+10)^2*(2400000*exp(-83*m)). The exponential addition law first makes the left side exactly m*(gamma+10)^2*(240000*exp(-83*m)); nonnegativity of m and (gamma+10)^2 then gives the stated relaxation. This consequence is exposition of an existing application, with an anonymous transient exact check; it has no retained named declaration or theorem Describe. The proof of the full mean bound instead uses shell_exp_constant240, the exact identity with coefficient 240, through complete_real_line_mean_bound.

**Theorem 1.1 (Complete multiplicity-preserving weighted mean).**

$$\forall Z \in \operatorname{CompleteZeroFamily}\left(\right),\; \forall m \in \mathbb{R},\; \forall gamma \in \mathbb{R},\; \operatorname{LowHCertificates}\left(Z, m, \mathit{gamma}\right) \Rightarrow \left(\operatorname{IntegrableOn}\left(\operatorname{lowHIntegrand}\left(Z, m, \mathit{gamma}\right), \operatorname{Ioi}\left(1\right)\right) \land \operatorname{norm}\left(\operatorname{lowHMean}\left(Z, m, \mathit{gamma}\right)\right) \le m \cdot \operatorname{D}\left(\mathit{gamma}\right)^{2} \cdot \left(2400000 \cdot \operatorname{exp}\left(0 - 83 \cdot m\right) + 2400 + 384 \cdot \operatorname{exp}\left(0 - 28 \cdot m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/CompleteLowHWeightedSpectralMean.complete_low_h_weighted_mean_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary complete indexed family, the LowHCertificates hypothesis is exactly m >= 1 and gamma > 10. The conclusion first gives IntegrableOn over y in (1,infinity), then bounds the norm of lowHMean by m*(gamma+10)^2*(2400000*exp(-83*m) + 2400 + 384*exp(-28*m)).

The proof retains the full h interval [0,2] with weight 1+h and integral 4, the Gaussian center 16*m and denominator 4*m, physical coefficient 3, all natural-index multiplicities, and both imaginary signs. The shell path supplies 20, the h integral supplies 4, and the physical coefficient supplies 3; the named extensions supply 2400 and 384*exp(-28*m), while the shell decay is 2400000*exp(-83*m). No finite or truncated replacement, assumed final bound, critical-line premise, Robin conclusion, QGP conclusion, or RH conclusion is part of this declaration.

## References

- Truth anchor: `D5/S3/Arith/Robin/CompleteLowHWeightedSpectralMean.complete_low_h_weighted_mean_bound`
- Dependency: [D5/S3/Arith/Robin/CompleteLowHWeightedGaussianMean](CompleteLowHWeightedGaussianMean.md)
