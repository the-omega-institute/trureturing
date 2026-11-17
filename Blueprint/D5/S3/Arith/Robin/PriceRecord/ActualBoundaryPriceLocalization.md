# Conditional BHP boundary-price localization

## Abstract

Conditional BHP boundary-price localization.

**Theorem 1.1 (Uniform pools around the first prime).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.uniform_counted_first_pools`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.uniform_counted_first_pools` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed j>=2 and positive count constants C,c, one threshold gives lower and strict upper prime pools of cardinality ceil(P^(19/(40*j))) around every sufficiently large natural P. Their radius C*P^(21/40) is nonnegative and at most P/2. The complete count hypothesis quantifies over every real x beyond its threshold.

**Theorem 1.2 (Higher-layer capacity and legal valuation bands).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.uniform_higher_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.uniform_higher_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed j>=2 and positive C,c, one threshold precedes all full records and original positive prices. The higher-layer root Q supplies the requested cardinality plus the endpoint allowance in radius C*Q^(21/40); the neighboring layers lie outside the comparison bands, and P<=Q^j. The argument combines the existing record ratio and scale limits on the same integer.

**Theorem 1.3 (Lower bound for the first price).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.first_beta_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.first_beta_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real P>=2, 1/(P*log(P))<=2*beta(1,P). The elementary logarithm lower bound controls the actual first marginal price, rather than replacing it by an asymptotic reference price.

**Theorem 1.4 (A common logarithmic scale for the variation bound).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.priceLip_half_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.priceLip_half_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Q>=4, P>1 and D>0 with log(P)/D<=log(Q/2), priceLip(j,Q/2) is bounded by ((j+2)*2^(j+1)*D)/(Q^(j+1)*log(P)). This translates the local price variation to the first-prime logarithmic scale.

**Theorem 1.5 (Conditional actual boundary-price localization).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.bhp_boundary_price_localization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.bhp_boundary_price_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the literal BHPMaximumGap and the independent two-sided BHPShortIntervalCount, both at exponent 21/40. For every fixed j>=2 there are positive C,T before all m>=2 and all original mu>0. If every positive n<m has strictly smaller goldenResourceObjective(mu,n), and P=largestPrime(m)>=T, then abs(beta(j,layerPrime(m,j))-beta(1,P))<=C*beta(1,P)*P^(-19/(40*j)). Actual finite exchanges use the original valuations, including valuation excess. The count route does not infer the count hypothesis from the maximum-gap hypothesis. The statement is conditional: neither analytic supplier is proved here, and it establishes neither full bank payment nor Robin or RH.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.bhp_boundary_price_localization`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.first_beta_lower`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.priceLip_half_bound`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.uniform_counted_first_pools`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.uniform_higher_geometry`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry](ActualBoundaryPriceGeometry.md)
