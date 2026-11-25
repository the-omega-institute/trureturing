# Finite integer activation at a fixed price

## Abstract

Exact capped activation and a finite bound for all omitted integer Robin layers.

**Theorem 1.1 (The capped activation formula is attained).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedLayerFiniteActivation.capped_minimum_isLeast`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedLayerFiniteActivation.capped_minimum_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a prime p, a real charge q, and a natural cap K ≥ 1. The cost of exponent a is q(a − 1) plus the Euler term −log(1 − p^(-(a+1))). For 1 ≤ a ≤ K the least cost is the Euler term at K plus the sum over 2 ≤ j ≤ K of min(q, d_j), where d_j is the Euler term at j − 1 minus the Euler term at j.

The exact marginal d_j is the golden layer marginal times log p, so the strictly profitable layers form an initial segment. Choose its last index, or exponent one if it is empty. Telescoping the remaining Euler increments gives the formula at this exponent. An equal charge and marginal can be placed on either side of the split.

**Theorem 1.2 (Prime-dependent caps bound all omitted layers).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedLayerFiniteActivation.fixed_price_omitted_layers`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedLayerFiniteActivation.fixed_price_omitted_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite prime support S and positive price λ, use charge q_p = λ log p. The fixed-price minimum is over all natural vectors whose exponents are at least one on S. Subtract the sum over S of the clipped marginals through layer m ≥ 2. The difference is nonnegative and is at most the sum over S of (K(p) − m)q_p plus the Euler term at K(p), for arbitrary caps K(p) ≥ m.

The uncapped integer optimum is attained at each prime, so the supported minimum is the sum of the local minima. Every local cost dominates the retained clipped sum. Restricting to the capped interval gives the other inequality, with each extra clipped layer bounded by one charge.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedLayerFiniteActivation.capped_minimum_isLeast`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedLayerFiniteActivation.fixed_price_omitted_layers`
- Dependency: [D5/S3/Arith/GoldenResourceOptimalInteger](../../GoldenResourceOptimalInteger.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice](BoundaryPrimePrice.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedSupportIntegerActivationEnvelope](FixedSupportIntegerActivationEnvelope.md)
