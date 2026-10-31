# Actual Full-Record Third-Layer Mass

## Abstract

The entire mass of actual layers at least three is uniformly negligible on the root scale for full positive-price records.

**Theorem 1.1 (Finite bound on the literal integer).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualThirdLayerMass.price_record_third_layer_mass_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualThirdLayerMass.price_record_third_layer_mass_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m>=2, lambda>=0, P=OriginalEndpointPrimeTail.largestPrime(m), and Q3=FixedLayerRigidity.layerPrime(m,3). Assume the original strict predecessor record: for every positive integer n<m, goldenResourceObjective(lambda,n)<goldenResourceObjective(lambda,m). The objective is log(sigma(n)/n)-lambda*log(n). Use the existing strict_inventory_third_layer_mass(m), namely R3=sum over actual prime divisors p with a_p>=3 of (a_p-2)*log(p), where a_p is the actual valuation of m. The theorem proves 0<=R3<=Q3*log(4*P^2).

The prime-power envelope of PrimePowerEnvelope supplies p^a_p<4*P^2 for every occupied prime, at this same integer and price. Thus each nonnegative summand is at most a_p*log(p)=log(p^a_p)<log(4*P^2). The actual third-layer prime support lies in the integer interval [1,Q3], whose cardinality is Q3. Summing this uniform bound gives the finite estimate. Nonnegativity is proved within the same theorem. No initial-support or antitonicity assumption is needed for this count.

An empty third layer has Q3=1 by the existing definition and R3=0. The interval-cardinality proof includes that case and every small record without a cutoff exception. The integer, factorization, largest prime and layer prime all remain the original ones.

**Theorem 1.2 (Uniform disappearance at root scale).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualThirdLayerMass.price_record_third_layer_mass_vanishing`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualThirdLayerMass.price_record_third_layer_mass_vanishing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0 there is a real T>0 such that every m>=2 and every lambda>0 with the full strict predecessor record and P>=T satisfy R3/sqrt(P)<epsilon. The same T works for all prices and all records in this class. In combination with nonnegativity, this is the uniform absolute-value limit R3/sqrt(P)->0.

Apply FixedLayerRigidity.price_record_fixed_layer_rigidity at j=3 with error one. Eventually Q3^3/P<4, hence Q3<=2*P^(1/3). The finite theorem is consumed to bound the normalized mass by 2*P^(1/3)*log(4*P^2)/sqrt(P). Expanding the logarithm and combining the real powers expresses this bound as 2*log(4)*P^(-1/6)+4*log(P)/P^(1/6), which tends to zero by the existing real-power and logarithm asymptotics.

These are estimates for actual full predecessor records, with no colossal-abundance, global optimizer, special-price, optimalLayerCount or RH-sized theta(P)-P premise. The older strict inventory third-layer bound has an optimalLayerCount hypothesis and is not applied here. No maximum-exponent asymptotic is used.

Together with the actual second-layer asymptotic and ordinary PNT, this vanishing remainder supplies the second sqrt(2) correction needed in the signed Robin coefficient 2*sqrt(2). This module proves the remainder estimate, not that combined signed formula. Signed prime-error upper control, Robin's inequality and RH remain open. No historical novelty is claimed.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualThirdLayerMass.price_record_third_layer_mass_bound`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualThirdLayerMass.price_record_third_layer_mass_vanishing`
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerRigidity](FixedLayerRigidity.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PrimePowerEnvelope](PrimePowerEnvelope.md)
