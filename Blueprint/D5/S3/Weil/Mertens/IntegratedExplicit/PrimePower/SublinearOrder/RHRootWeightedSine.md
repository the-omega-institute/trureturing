# The inclusive positive-ordinate cutoff

## Abstract

The weighted sine approximation to the RH root signal

Under Mathlib's Riemann hypothesis, each distinct positive ordinate γ identifies a unique zero. Write mγ for its analytic multiplicity. The weight is wγ = mγ γ/(1/4 + γ²). For 0 < γ ≤ T the sum of these weights is W(T) and the sum of wγ sin(γv) is S(T,v). Write P(T) for the real supremum of S(T,v) over real v. `D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum`

**Theorem 1.1 (Harmonic mass).**

$$\mathit{RH} \Rightarrow \operatorname{Tendsto}\left((\lambda T \mapsto \frac{\operatorname{W}\left(T\right)}{\operatorname{log}\left(T\right)^{2}}), \mathit{atTop}, \operatorname{nhds}\left(\frac{1}{4 \cdot \pi}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine.harmonic_mass_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At t = 1/T the signed quarter-phase sine slope has the known leading term t log²(T)/(2π). Its Taylor approximation equals 2t W(T) and differs from the slope by at most a constant times t(1 + log T). The count through the inclusive cutoff controls the quadratic Taylor error and the inverse-square tail controls the rest. `D5/S3/Weil/ZeroData/ZetaOrdinatePhaseStiffness` `D5/S3/Weil/Mertens/ZeroAbscissaPower`

**Theorem 1.2 (Bounds for the real supremum).**

$$\mathit{RH} \Rightarrow \left(\forall T \in \mathbb{R},\; 0 \le \operatorname{P}\left(T\right) \land \operatorname{P}\left(T\right) \le \operatorname{W}\left(T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine.weighted_sine_sup_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value at zero is zero. Each sine has absolute value bounded by one and each weight is nonnegative.

**Theorem 1.3 (Uniform upper bound and cofinal signed lower bound).**

$$\mathit{RH} \Rightarrow \left(\forall r \in \mathbb{R},\; 1 < r \Rightarrow \left(\exists C \in \mathbb{R},\; 0 \le C \land \left(\forall h \in \mathbb{R},\; \left(0 < h \land h \le \frac{1}{\operatorname{exp}\left(1\right)}\right) \Rightarrow \left(\left(\forall u \in \mathbb{R},\; \left|\operatorname{Delta}\left(r, h, u\right)\right| \le \operatorname{B}\left(r, h\right) + \operatorname{E}\left(C, h\right)\right) \land \left(\forall U \in \mathbb{R},\; \forall b \in \mathbb{R},\; b < \operatorname{B}\left(r, h\right) - \operatorname{E}\left(C, h\right) \Rightarrow \left(\exists u \in \mathbb{R},\; U \le u \land b < \operatorname{Delta}\left(r, h, u\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine.root_signal_weighted_sine_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real r > 1 use s(r) = 1/2 − 1/(2r), and let R(r,u) be the centered normalized root signal. The difference Δ(r,h,u) is R(r,u+h) − R(r,u). Write B(r,h) = (2h/s(r)) P(r/h) and E(C,h) = C h log(1/h).

The coefficient correction multiplied by the ordinate is absolutely summable, so the correction contributes at most order h. The Taylor bound for the leading coefficients is uniform in phase. Pairing conjugate occurrences gives the approximation (2h/s(r)) S(r/h,u/r), with analytic multiplicities retained. `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement`

Oddness makes the supremum of the absolute polynomial equal to its signed supremum. Each real orbit point is a cluster point at arbitrarily late times. The finite polynomial is a continuous readout of the occurrence phases, so every strict lower threshold below B(r,h) − E(C,h) has a sufficiently late signed return. `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster`

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine.harmonic_mass_limit`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine.root_signal_weighted_sine_return`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine.weighted_sine_sup_bounds`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement](RHRootQuarterPhaseIncrement.md)
- Dependency: [D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum](../../../../ZeroData/PositiveOrdinateSpectrum.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster](../../PrimePhaseCluster.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement](RHRootQuarterPhaseIncrement.md)
- Narrative reference: [D5/S3/Weil/Mertens/ZeroAbscissaPower](../../../ZeroAbscissaPower.md)
- Narrative reference: [D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum](../../../../ZeroData/PositiveOrdinateSpectrum.md)
- Narrative reference: [D5/S3/Weil/ZeroData/ZetaOrdinatePhaseStiffness](../../../../ZeroData/ZetaOrdinatePhaseStiffness.md)
