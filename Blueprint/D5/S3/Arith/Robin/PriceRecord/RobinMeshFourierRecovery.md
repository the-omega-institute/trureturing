# Fourier recovery from canonical Robin records

## Abstract

Centered Robin samples recover literal zeta-zero multiplicity on a closed upper line.

**Theorem 1.1 (Recovery of the analytic multiplicity coefficient).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinMeshFourierRecovery.actual_canonical_samples_fourier_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinMeshFourierRecovery.actual_canonical_samples_fourier_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix w in ℂ with 1/2≤Re(w)<1 and assume Re(ρ)≤Re(w) for every nontrivial zeta zero ρ. Let N be a strictly increasing sequence in ℕ with N(0)>0 and N(k+1)/N(k)→1 in ℝ. Put y(k)=log(N(k)) and m(k)=strictInteger(firstLayerPrice(N(k)+1)). Write c(w)=2√2−2 if Re(w)=1/2 and c(w)=0 otherwise. For M>0 take the weighted average of the first M samples of (N(k)^(1−Re(w)) log(N(k)) robinLogMargin(m(k))−c(w)) exp(−i Im(w)y(k)), with weights y(k+1)−y(k) and divisor y(M)−y(0). As M→∞ this tends to −ord_w(ζ)/(w(1−w)) in ℂ, where ord_w(ζ) is analyticOrderNatAt riemannZeta w.

The signed canonical sample asymptotic gives the negative of the complete normalized actual zero series up to an error tending to zero. The ratio-one condition supplies vanishing log gaps, and the closed-strip Fourier theorem selects the occurrences at w after demodulation. Each occurrence of ρ supplies 1/(ρ(1−ρ)) to the zero series. The occurrence enumeration and the analytic-order identity count exactly ord_w(ζ) occurrences at w. If ζ(w)≠0, the limit is zero.

The pointwise lower-bound criterion for an unattained upper abscissa remains open here.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinMeshFourierRecovery.actual_canonical_samples_fourier_recovery`
- Dependency: [D5/S3/Analytic/Asymptotics/GapWeightedFourier](../../../Analytic/Asymptotics/GapWeightedFourier.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap](RobinVanishingRelativeGap.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace](../../../Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.md)
