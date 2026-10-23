# Actual optimizers and two-price defects

## Abstract

Complete original prime-layer optimizers and their two-price pressure identity.

The objective is log(sigma(n)/n)-q*log(n). The strict integer selects every layer with marginal greater than q; the maximal integer also includes every equality layer. All primes, positive layers and simultaneous ties are retained.

**Theorem 1.1 (The complete maximal optimizer).**

Lean statement: `D5/S3/Arith/Robin/ActualTwoPriceDefect.maximalInteger_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.maximalInteger_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real price, the weak layer set is finite and each prime fiber is a complete initial interval. Its finite exponent product is positive, has the stated exponents, and is the greatest original optimizer in the stated order. Finiteness and optimality follow from the existing marginal decay and local threshold suppliers, without a finite prime or exponent truncation hypothesis.

**Theorem 1.2 (Pressure across all activation events).**

Lean statement: `D5/S3/Arith/Robin/ActualTwoPriceDefect.pressure_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.pressure_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a,b>1, the oriented integral of clock(u)*weight(u) is pressure(price(b))-pressure(price(a)). Here price(u)=1/(u*log(u)), weight(u)=(1+log(u))/(u^2*log(u)^2), and clock(u) is the logarithm of the same strict optimizing integer. Compact layer support proves stability on the correct side of a tie. The one-sided derivative and integrability are proved before the fundamental theorem of calculus is applied.

**Theorem 1.3 (Keep the source integer at both prices).**

Lean statement: `D5/S3/Arith/Robin/ActualTwoPriceDefect.two_price_oriented`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.two_price_oriented` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x,a>1, the actual defect of integerAt(x) at price(a) equals the oriented integral from x to a of (clock(u)-clock(x))*weight(u). The source integer is retained rather than replaced by an independently chosen inventory.

**Theorem 1.4 (The same cost for every comparison optimizer).**

Lean statement: `D5/S3/Arith/Robin/ActualTwoPriceDefect.npc5_any_comparison_optimizer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.npc5_any_comparison_optimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When A=clock(x)>1, every positive original optimizer at price(A), including the maximal tied optimizer, has objective gain over integerAt(x) equal to the integral from min(x,A) to max(x,A) of |clock(u)-clock(x)|*weight(u). Clock monotonicity pays both price orders. This exact defect identity does not supply the strict Robin endpoint sign.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.maximalInteger_spec`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.npc5_any_comparison_optimizer`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.pressure_integral`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.two_price_oriented`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison](../GoldenResource/GoldenResource5040EndpointComparison.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount](../GoldenResource/GoldenResourceOptimalLayerCount.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion](../GoldenResource/GoldenResourceThresholdCriterion.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerPhaseSeparation](EulerLayerPhaseSeparation.md)
