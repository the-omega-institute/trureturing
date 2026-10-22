# Complete Low-Height Weighted Gaussian Mean

## Abstract

Absolute convergence makes the complete indexed Gaussian moment and extension identity valid.

CompleteZeroFamily is indexed by all natural numbers; its zero map may repeat a value. The open strip, absolute height above 10, summable reciprocal squares with total below 2, finite inclusive shells and two-sided count floor(2*T^2) retain every analytic multiplicity and both imaginary signs.

The resolvent is bounded by the reciprocal square of the imaginary part. For every real y and every h in [0,2], the exponential norm is at most exp(y)+exp(-2*y). The two Gaussian endpoints give an integrable product majorant for the complete norm series. Bochner integrability is proved before the sum and integral commute.

For m >= 1, finite subsets of the natural index are partitioned by floor(abs(Im(zero n))-10). The two-sided count and a geometric majorant yield summability of shellWeight m (zero n) over all n and shellSum Z m <= 10000*exp(-100*m). The finite subsets are a proof device for the infinite sum.

For every CompleteZeroFamily Z, every real m > 0 and every real gamma, complete_zero_lowH_integrable proves IntegrableOn (lowHIntegrand Z m gamma) on (1,infinity). Its source owner is CompleteLowHWeightedGaussianMean, with the preserved CompleteLowHWeightedSpectralMean Lean namespace. The proof takes complete_zero_lowH_product_integrable, applies integral_prod_left and moves the fixed physical envelope outside the h integral. The product proof uses the full reciprocal-square norm series and both Gaussian exponential endpoints. This exact integrability fact supplies the first conjunct of the final weighted theorem.

**Theorem 1.1 (Integrability and exact complete full-line mean).**

$$\forall Z \in \operatorname{CompleteZeroFamily}\left(\right),\; \forall m \in \mathbb{R},\; \forall gamma \in \mathbb{R},\; 0 < m \Rightarrow \left(\operatorname{Integrable}\left(\operatorname{lowHIntegrand}\left(Z, m, \mathit{gamma}\right)\right) \land \operatorname{integral}\left(y, \mathbb{R}, \operatorname{lowHIntegrand}\left(Z, m, \mathit{gamma}, y\right)\right) = \operatorname{completeRealLineMean}\left(Z, m, \mathit{gamma}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/CompleteLowHWeightedGaussianMean.complete_zero_fullLine_integrable_and_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m > 0 and arbitrary real gamma, the physical integrand is integrable on the whole real line and its integral equals the complete countable shell mean. The full complex cubic Gaussian identity retains center 16*m, the +2*z correction, the physical coefficient 3 and the actual weight 1+h.

**Theorem 1.2 (The exact extension identity).**

$$\forall Z \in \operatorname{CompleteZeroFamily}\left(\right),\; \forall m \in \mathbb{R},\; \forall gamma \in \mathbb{R},\; 0 < m \Rightarrow \operatorname{lowHMean}\left(Z, m, \mathit{gamma}\right) = \operatorname{completeRealLineMean}\left(Z, m, \mathit{gamma}\right) + \operatorname{positiveExtension}\left(Z, m, \mathit{gamma}\right) + \operatorname{negativeExtension}\left(Z, m, \mathit{gamma}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/CompleteLowHWeightedGaussianMean.complete_zero_fubini_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive extension is minus the integral over (0,1]; the negative extension is minus the integral over (-infinity,0). Whole-line integrability justifies the partition; the omitted singleton at zero is null. No finite truncation or additional analytic certificate is required.

## References

- Truth anchor: `D5/S3/Arith/Robin/CompleteLowHWeightedGaussianMean.complete_zero_fubini_exchange`
- Truth anchor: `D5/S3/Arith/Robin/CompleteLowHWeightedGaussianMean.complete_zero_fullLine_integrable_and_moment`
- Dependency: [D5/S3/Arith/Robin/CompleteCoefficientLaplace](CompleteCoefficientLaplace.md)
- Dependency: [D5/S3/Arith/Robin/CompleteLowHGaussianMoment](CompleteLowHGaussianMoment.md)
- Dependency: [D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment](../../Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment.md)
