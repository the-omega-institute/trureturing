# The power-saving gap criterion and its polynomial specialization

## Abstract

Canonical records on integer meshes characterize the closed zero strip

**Theorem 1.1 (Strictly increasing natural meshes with a power-saving gap).**

$$\forall N \in \mathbb{N} \to \mathbb{N},\; \operatorname{StrictMono}\left(N\right) \Rightarrow \left(\forall G \in \mathbb{R},\; \forall eta \in \mathbb{R},\; 0 \le G \Rightarrow \left(0 < eta \Rightarrow \left(\left(\exists K \in \mathbb{N},\; \forall k \in \mathbb{N},\; K \le k \Rightarrow \operatorname{cast}\left(N\left(k + 1\right)\right) - \operatorname{cast}\left(N\left(k\right)\right) \le G \cdot \operatorname{rpow}\left(\operatorname{cast}\left(N\left(k\right)\right), 1 - eta\right)\right) \Rightarrow \left(\forall alpha \in \mathbb{R},\; 0 < alpha \Rightarrow \left(alpha \le \frac{1}{2} \Rightarrow \left(\left(\exists M \in \mathbb{R},\; 0 \le M \land \left(\exists K \in \mathbb{N},\; \forall k \in \mathbb{N},\; K \le k \Rightarrow -M \le \operatorname{rpow}\left(\operatorname{cast}\left(N\left(k\right)\right), alpha\right) \cdot \operatorname{log}\left(\operatorname{cast}\left(N\left(k\right)\right)\right) \cdot \operatorname{robinLogMargin}\left(\operatorname{strictInteger}\left(\operatorname{firstLayerPrice}\left(\operatorname{cast}\left(N\left(k\right)\right) + 1\right)\right)\right)\right)\right) \Leftrightarrow \left(\forall rho \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(rho\right) \Rightarrow \operatorname{re}\left(rho\right) \le 1 - alpha\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion.result_of_power_saving_gaps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each strictly increasing mesh N of natural numbers with the displayed eventual gap bound and each real 0<alpha<=1/2, the eventual Robin lower bound is equivalent to Re(rho)<=1-alpha for every actual nontrivial zeta zero. The sample is strictInteger(firstLayerPrice(N(k)+1)). This is the least full golden-resource optimizer, with every prime-power layer considered and cutoff-equal layers excluded. Taking N(k)=k and G=eta=1 gives the criterion on the full natural tail, including prime cutoffs.

For the lower-bound-to-strip direction, let Theta be the supremum of actual zero real parts and suppose Theta>1-alpha. Set delta=min(eta,1), choose max(1-alpha,Theta-delta)<sigma<Theta, and put a=1-sigma, epsilon=(sigma+delta-Theta)/2 and beta=Theta+epsilon. sample_exponent_lower transfers the same M to weight a. For N(k)>=12, half_shift_cutoff and continuity of price give X(k) strictly between N(k)+1 and N(k)+3/2, with price(X(k))=firstLayerPrice(N(k)+1). At this point the pressure potential bounds the sampled margin from above, and the weight comparison gives the pressure sample bound with constant 4*M.

The exact-price points form a strictly increasing real mesh tending to infinity. Its eventual gap bound uses G+1/2 and delta. clock_power bounds the discrepancy of the complete clock with exponent beta, and a+beta-delta<=1 allows pressure_mesh_samples_to_all to give an all-real pressure lower bound. The choice of sigma applies also when Theta=1 or the supremum is unattained.

At the actual integer clock, the pressure potential is at most the record margin. The eventual bounds P/2<=theta(P)<=log(m) for P=largestPrime(m) and record_weight transfer the lower bound to original strict records. margin_identity, fullC_leading and B_prefix then give an all-real lower envelope for B through the canonical prime-prefix normalization. B_lower_envelope_strip uses critical_theta_tail_peak to force Theta<=sigma, contradicting the choice of sigma.

For the strip-to-lower-bound direction, actual_B_critical_strip_envelope applies at alpha, including alpha=1/2. Strict increase sends N(k) and its canonical prime prefix to infinity. fullC_leading gives an eventually nonnegative arithmetic correction, so margin_identity and B_prefix bound the sampled margin below by B(N(k)).

**Theorem 1.2 (The closed zero strip criterion on the powers k^r).**

$$\forall r \in \mathbb{N},\; 2 \le r \Rightarrow \left(\forall alpha \in \mathbb{R},\; 0 < alpha \Rightarrow \left(alpha \le \frac{1}{2} \Rightarrow \left(\left(\exists M \in \mathbb{R},\; 0 \le M \land \left(\exists K \in \mathbb{N},\; 2 \le K \land \left(\forall k \in \mathbb{N},\; K \le k \Rightarrow -M \le \operatorname{rpow}\left(\operatorname{cast}\left(\operatorname{pow}\left(k, r\right)\right), alpha\right) \cdot \operatorname{log}\left(\operatorname{cast}\left(\operatorname{pow}\left(k, r\right)\right)\right) \cdot \operatorname{robinLogMargin}\left(\operatorname{strictInteger}\left(\operatorname{firstLayerPrice}\left(\operatorname{cast}\left(\operatorname{pow}\left(k, r\right)\right) + 1\right)\right)\right)\right)\right)\right) \Leftrightarrow \left(\forall rho \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(rho\right) \Rightarrow \operatorname{re}\left(rho\right) \le 1 - alpha\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural r>=2, take N(k)=k^r, G=r*2^(r-1) and eta=1/r in result_of_power_saving_gaps. power_strictMono and polynomial_gap give the two mesh hypotheses. The sample remains the strict record at firstLayerPrice(k^r+1), with the weight evaluated at k^r. An eventual bound gives the displayed threshold by replacing it with its maximum with 2. The zero condition includes the boundary Re(rho)=1-alpha.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion.result`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion.result_of_power_saving_gaps`
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
