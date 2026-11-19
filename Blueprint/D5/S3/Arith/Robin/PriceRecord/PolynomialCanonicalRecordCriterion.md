# The full polynomial sampling criterion

## Abstract

Polynomial canonical records characterize the closed zero strip

**Theorem 1.1 (All natural powers and all real strip exponents).**

$$\forall r \in \mathbb{N},\; 2 \le r \Rightarrow \left(\forall alpha \in \mathbb{R},\; 0 < alpha \Rightarrow \left(alpha \le \frac{1}{2} \Rightarrow \left(\left(\exists M \in \mathbb{R},\; 0 \le M \land \left(\exists K \in \mathbb{N},\; 2 \le K \land \left(\forall k \in \mathbb{N},\; K \le k \Rightarrow -M \le \operatorname{rpow}\left(\operatorname{pow}\left(k, r\right), alpha\right) \cdot \operatorname{log}\left(\operatorname{pow}\left(k, r\right)\right) \cdot \operatorname{robinLogMargin}\left(\operatorname{strictInteger}\left(\operatorname{firstLayerPrice}\left(\operatorname{pow}\left(k, r\right) + 1\right)\right)\right)\right)\right)\right) \Leftrightarrow \left(\forall rho \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(rho\right) \Rightarrow \operatorname{re}\left(rho\right) \le 1 - alpha\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural r>=2 and each real 0<alpha<=1/2, one nonnegative constant M bounds all sufficiently late natural samples. The sampled integer is strictInteger(firstLayerPrice(k^r+1)); strictInteger is the least full golden-resource optimizer, with every prime-power layer retained and equality excluded at the strict cutoff. robinLogMargin has its original arithmetic definition. The right side quantifies over every actual nontrivial zeta zero, including the closed boundary Re(rho)=1-alpha. This criterion does not prove RH or the sample lower bound.

Write W(a,X)=X^a*log(X) and S(X)=EulerGamma+log(log(X))-1/log(X)-pressure(price(X)). The complete pressure FTC gives the compact-interval modulus |S(b)-S(a)|<=E*(price(a)-price(b)) when |u-clock(u)|<=E on [a,b]. The primitive derivative is u*weight(u); the clock integrand uses the original complete inventory. The polynomial mesh has endpoints N=k^r and (k+1)^r, width at most r*2^(r-1)*N/k, and a fixed multiplicative enclosure. These estimates fill all real X, with no public mesh hypothesis.

For the lower-bound-to-strip direction, let Theta be the supremum of actual zero real parts. If Theta>1-alpha, choose max(1-alpha,Theta-1/r)<sigma<Theta and set a=1-sigma, epsilon=(sigma+1/r-Theta)/2>0, beta=Theta+epsilon. The same M descends from alpha to a because 0<N^(a-alpha)<=1 and M>=0. Only the difference between two margins with the same prime prefix uses the existing square-root normalization; W/D<=1 scales that difference. The full clock discrepancy is O(X^beta), and a+beta-1-1/r=-epsilon pays the mesh error. Beta may exceed one; Theta=1 and an unattained supremum are included.

Pressure at the actual integer clock is at most its margin. For every original strict predecessor record, log(m)>=theta(P)>=P/2 eventually, where P=largestPrime(m). Thus W(a,P)<=4*W(a,log(m)), and sign-sensitive rescaling transports the all-real pressure lower bound to all original records. The exact margin_identity, fullC_leading and B_prefix then give an all-real lower B envelope. The correction upper bound is scaled before normalization, without assuming its sign. The proved canonical prime-prefix normalization transfers the fixed nonpositive constant. The exact one-sided B converse forces Theta<=sigma, a contradiction.

For the strip-to-lower-bound direction, actual_B_critical_strip_envelope is used at the original alpha. The full arithmetic correction is eventually positive at all these actual records. The exact prime-prefix B identity then bounds each margin below by B(k^r). This direction needs no PNT normalization ratio and retains alpha=1/2. All constants and thresholds may depend on r and alpha; no finite surrogate replaces either natural tail quantifier or the full zero strip.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion.result`
- Dependency: [D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure](../ActualPriceRecordPrimeStructure.md)
- Dependency: [D5/S3/Arith/Robin/ActualRobinInterval](../ActualRobinInterval.md)
- Dependency: [D5/S3/Arith/Robin/ActualTwoPriceDefect](../ActualTwoPriceDefect.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ThetaReparametrizedSandwich](../Analytic/ThetaReparametrizedSandwich.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope](../Analytic/ZeroFreeStripMertensEnvelope.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerInventoryGrowth](../EulerLayerInventoryGrowth.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/KappaGap](../ForwardKernel/KappaGap.md)
- Dependency: [D5/S3/Arith/Robin/LogarithmBounds](../LogarithmBounds.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualBalancedCutoff](ActualBalancedCutoff.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry](ActualBoundaryPriceGeometry.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/OriginalRecordLowerBoundCriterion](OriginalRecordLowerBoundCriterion.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds](PolynomialMeshBounds.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin](RHSharpOriginalRecordMargin.md)
- Dependency: [D5/S3/Weil/Mertens/ActualThetaTailLaplace](../../../Weil/Mertens/ActualThetaTailLaplace.md)
- Dependency: [D5/S3/Weil/Mertens/CriticalThetaTailPeak](../../../Weil/Mertens/CriticalThetaTailPeak.md)
- Dependency: [D5/S3/Weil/Mertens/ZeroAbscissaPower](../../../Weil/Mertens/ZeroAbscissaPower.md)
- Dependency: [D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction](../../../Weil/ZeroInfinitude/ExplicitFormulaObstruction.md)
