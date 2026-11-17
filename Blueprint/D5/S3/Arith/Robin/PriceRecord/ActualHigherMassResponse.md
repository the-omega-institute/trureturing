# Actual all-layer canonical mass response from integer counting

## Abstract

Actual all-layer canonical mass response from integer counting.

At the two prices eta_minus=(1-s)lambda_X and eta_plus=(1+s)lambda_X, subtract the literal finite canonical coordinate sets. Their layer primes lie exactly in the half-open interval [x_plus,x_minus): a prime at the upper-price root counts; one at the lower-price root does not. Grouping this actual coordinate difference by layer, every integer interval has at most movement+1 points, all counted logarithms are <=log X, the total movement is <=333s sqrt X, and there are at most 6 log X layers. This derives, rather than assumes, the response <=400(s sqrt X log X+log^2 X). The construction includes boundary clamping and simultaneous ties across layers.

**Theorem 1.1 (actual higher mass response).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassResponse.actual_higher_mass_response`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassResponse.actual_higher_mass_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem actual_higher_mass_response {X s : ℝ} (hX : exp 2 ≤ X) (hs : 0 < s) (hs2 : s ≤ 1 / 2) : 0 ≤ higherMass (strictInteger ((1 - s) * referencePrice X)) - higherMass (strictInteger ((1 + s) * referencePrice X)) ∧ higherMass (strictInteger ((1 - s) * referencePrice X)) - higherMass (strictInteger ((1 + s) * referencePrice X)) ≤ 400 * (s * sqrt X * log X + log X ^ 2)

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassResponse.actual_higher_mass_response`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality](CompleteHigherInventoryDuality.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff](HigherLayerClampedCutoff.md)
