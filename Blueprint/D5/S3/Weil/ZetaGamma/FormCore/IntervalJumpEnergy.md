# Finite Gamma jump energy with endpoint jumps

## Abstract

Interval Lipschitz regularity controls the actual Gamma jump density, including both endpoint jumps, for arbitrary complex interval data.

Fix d>0, an interval I=(t,t+d], and a complex map u that is K-Lipschitz on [t,t+d]. Compact continuity gives a finite B with |u(x)|<=B on that closed interval. Write F=1_I u and E(s)=integral_R |F(x)-F(x-s)|^2 dx. No condition relates the endpoint values, and neither endpoint is required to vanish.

**Theorem 1.1 (The interior and both boundary strips).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/IntervalJumpEnergy.zeroTranslationEnergy_le_of_lipschitzOnWith`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/IntervalJumpEnergy.zeroTranslationEnergy_le_of_lipschitzOnWith` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s>0 the proof bounds the pointwise square by (K*s)^2 times 1_(t,t+d](x), plus B^2 times 1_(t,t+s](x), plus B^2 times 1_(t+d,t+d+s](x). If x and x-s are both in I, the Lipschitz estimate applies. If only x is in I then x-s<=t, so x is in the left strip. If only x-s is in I then x>t+d, so x is in the right strip. If neither is in I, the difference vanishes. The strips are allowed to overlap, and this proves the bound even when s>d.

All three majorant terms are integrable indicators of bounded intervals. More strongly, the existing zero_extension_memLp theorem and measurePreserving_sub_right show that F and F(.-s) are L2. Mathlib's memLp_two_iff_integrable_sq_norm makes the squared difference genuinely integrable before integral_mono is used. The three interval volumes are d, s and s, giving E(s)<=d*K^2*s^2+2*B^2*s. In particular, no arbitrary-L2 integral is used only through its totalized value.

**Theorem 1.2 (The actual singular density is integrable against this energy).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/IntervalJumpEnergy.zeroEnergyDensity_integrableOn_of_lipschitzOnWith`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/IntervalJumpEnergy.zeroEnergyDensity_integrableOn_of_lipschitzOnWith` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density is exactly rho(s)=exp(-s/2)/(1-exp(-2*s)). From exp(2*s)>=1+2*s one obtains (1+2*s)*exp(-2*s)<=1 and hence 1<=(1+1/(2*s))*(1-exp(-2*s)). The denominator is positive for s>0. Therefore rho(s)<=exp(-s/2)*(1+1/(2*s)). This is one global estimate: it retains the 1/s singularity and the exponential tail.

Put A=d*K^2. Multiplying the translation estimate and cancelling s, with s>0 explicitly recorded, gives 0<=rho(s)*E(s)<=exp(-s/2)*(A*s^2+(2*B^2+A/2)*s+B^2). The three terms are integrable on (0,infinity) by the pinned Mathlib theorem integrableOn_rpow_mul_exp_neg_mul_rpow with p=1, b=1/2 and exponents 2,1,0. No assumption of logarithmic frequency summability is involved.

For measurability, Lipschitz continuity on the closed interval supplies AEStronglyMeasurable u on I and compact boundedness supplies its L2 membership. The supplied PeriodicEnergyTransport.zeroTranslationEnergy_aestronglyMeasurable applies to precisely this interval input. The density is Borel measurable, and the product is measurable on (0,infinity). Integrable.mono' with the displayed nonnegative majorant proves IntegrableOn (DomainPassage.zeroEnergyDensity d t u) (Ioi 0).

## Smooth periodic windows and the physical Gamma endpoint

The smooth periodic applications start with an arbitrary complex u satisfying ContDiff R infinity u and Function.Periodic u L. In the pinned Mathlib, infinity is the smooth regularity order; the outer top denotes analytic regularity and is not used. ContDiffOn.exists_lipschitzOnWith on the compact convex closed interval supplies K directly. The interval theorem above derives henergy; compact continuity separately derives the exact MemLp premise. The complete supplied actual_zeroExtension_gamma_high_frequency_lower_bound is then applied with L>0, Ioc(-L/2,L/2), and every signed integer n satisfying natAbs(n)<M.

The application keeps all three supplied conclusions: integrability of mu(t)*normSq(paperFT F (t:C)); summability of gammaIncrement(angularFrequency n)*|physicalCoeff n|^2 over all integer n; and the full lower bound. Its signed mass constant is Re(digamma(1/4))-log(pi), its entire spectral tsum remains present, and its debit is (pi/2+L/(pi^2*(M-1))) times physical mass. The PLUS paperFT, the mu normalization and complex coefficients are inherited verbatim from the supplied endpoint.

For the original K_N(a), take L=2*a, M=N+1, a>0 and N>=1. The premise natAbs(n)<=N is exactly natAbs(n)<N+1, on both signs with no upper cutoff. The same complete conclusion is reproduced in a second transient example. The closed restriction [-a,a] and the Ioc representative differ at a Lebesgue null endpoint only; a third transient example records this actual a.e. equality. The smooth periodic function may have nonzero endpoint value, so zero extension still has jumps.

## Source ownership and remaining validation

The new analytic inference is the spatial strip partition followed by cancellation of the actual singular density. Compact-to-Lipschitz regularity and exponential-polynomial integrability are upstream Mathlib results and are used directly. The supplied one-mode theorem mode_actual_energy_integrable and the far-lattice theorem actualFarPair_integrable_and_le are not substitutes for this inference and are not used here. The spectral namespace is the one defined inside PeriodicEnergyTransport.lean.

The interval module has two public statements. Its private helpers have active consumers in those proofs. The exact endpoint applications remain anonymous examples and are not retained as a named bind-only Gamma theorem. Relative to the protected baseline and pinned upstream declarations, the source admission rationale is the substantive interval estimate and its actual-density domination; it does not confer admission on the supplied unfrozen Gamma closure. Lean checking, source admission, four-slot registration and publication are distinct obligations; this exposition alone certifies none of them. No zeroMode, completion-realization, numerical positive margin, final positivity or RH claim follows from this delivery.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/IntervalJumpEnergy.zeroEnergyDensity_integrableOn_of_lipschitzOnWith`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/IntervalJumpEnergy.zeroTranslationEnergy_le_of_lipschitzOnWith`
