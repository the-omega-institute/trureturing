# Three-band averaging after a low-frequency hit

## Abstract

Short-window averaging improves the loss bound for weighted sine recurrence.

Let I index a locally finite positive spectrum and let w(j) be its weights. Write W(T) for the sum of the weights at frequencies γ(j) ≤ T and S(T,v) for the sum of w(j) sin(γ(j)v) over the same indices. Eventually refers to the indicated real variable tending to positive infinity. `D5/S3/Analytic/Oscillation/OrdinateCounting`

**Theorem 1.1 (Uniform recurrence from low-frequency hits).**

$$\left(\forall j \in I,\; 0 \le \operatorname{w}\left(j\right)\right) \Rightarrow \left(\forall q \in \mathbb{R}\to\mathbb{R},\; \forall r \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall varepsilon \in \mathbb{R},\; \left(\left(0 < r \land 0 < \mathit{beta}\right) \land \left(\left(\operatorname{ContinuousAt}\left(q, \operatorname{min}\left(\mathit{beta}, 1\right)\right) \land \left(\forall p \in \mathbb{R},\; \left(0 < p \land p < 1\right) \Rightarrow \operatorname{Tendsto}\left((T \mapsto \frac{\operatorname{W}\left(T^{p}\right)}{\operatorname{W}\left(T\right)}), \mathit{atTop}, \operatorname{nhds}\left(\operatorname{q}\left(p\right)\right)\right)\right)\right) \land \left(\left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \operatorname{Eventually}\left((X \mapsto 0 < \operatorname{W}\left(X\right) \land \left(\forall a \in \mathbb{R},\; \exists u \in \mathbb{R},\; u \in [a, a + \operatorname{exp}\left(X\right)] \land 1 - \frac{\operatorname{S}\left(X, \frac{u}{r}\right)}{\operatorname{W}\left(X\right)} < e\right)), \mathit{atTop}\right)\right) \land 1 - \operatorname{q}\left(\operatorname{min}\left(\mathit{beta}, 1\right)\right) < \mathit{varepsilon}\right)\right)\right) \Rightarrow \operatorname{Eventually}\left((T \mapsto 0 < \operatorname{W}\left(T\right) \land \left(\forall a \in \mathbb{R},\; \exists u \in \mathbb{R},\; u \in [a, a + \operatorname{exp}\left(T^{\mathit{beta}}\right)] \land 1 - \frac{\operatorname{S}\left(T, \frac{u}{r}\right)}{\operatorname{W}\left(T\right)} < \mathit{varepsilon}\right)), \mathit{atTop}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/SpectrumThreeBandRecurrence.eventual_sine_three_band_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix r, β > 0 and put m = min(β,1). Assume the weights are nonnegative and that W(T^p)/W(T) tends to q(p) for every 0 < p < 1, with q continuous at m. For every tolerance e > 0 and all sufficiently large X, assume W(X) > 0 and that each interval of length exp(X) contains a point b with head loss 1 − S(X,b/r)/W(X) < e.

Choose 0 < α < κ < ν < m and e > 0 so that 1 + q(ν) − 2q(α) + e q(α) < ε. Continuity at m and the strict slack above 1 − q(m) permit this choice. For X = T^α, Y = T^ν and h = T^(−κ), start at the head hit b and apply the local point bound on [b,b+h]. It controls the score using head drift hX/r, the middle band mass W(Y) − W(X), and the tail factor 2r/(hY). `D5/S3/Fourier/HarmonicScoreLocalAverage`

After division by W(T), the head drift and tail errors tend to zero because α < κ < ν and the mass ratios have finite limits. The resulting upper bound on normalized loss tends to 1 + q(ν) − 2q(α) + e q(α). Since α < β, eventually exp(X) + h is at most exp(T^β). The eventual bounds are independent of a.

For the actual positive zeta ordinates under RH and Lamzouri's Conjecture 1.1 (Effective LI), use weights mγ γ/(1/4 + γ²), where mγ is the analytic multiplicity at γ. Effective LI supplies separation on each fixed coefficient box because the zero count eventually exceeds its bound. The distinct mode count is O(X log X). The weighted cutoff recurrence with exponent 1 then gives the head hits for every e > 0. The harmonic mass satisfies W(T)/log²(T) → 1/(4π), so q(p) = p². Thus for r, β > 0 and ε > 1 − min(β,1)², every interval of length exp(T^β) contains a point with normalized loss below ε for all sufficiently large T. `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine`

A singleton spectrum at frequency one with weight one has q(p) = 1. Its sine reaches one in every interval of length at least 2πr, so it satisfies the head-hit premise for each r > 0.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumThreeBandRecurrence.eventual_sine_three_band_recurrence`
- Dependency: [D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff](SpectrumPhaseCutoff.md)
- Dependency: [D5/S3/Fourier/HarmonicScoreLocalAverage](../../Fourier/HarmonicScoreLocalAverage.md)
- Narrative reference: [D5/S3/Analytic/Oscillation/OrdinateCounting](OrdinateCounting.md)
- Narrative reference: [D5/S3/Fourier/HarmonicScoreLocalAverage](../../Fourier/HarmonicScoreLocalAverage.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine](../../Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine.md)
