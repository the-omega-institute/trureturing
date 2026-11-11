# Missing and occupied prime blocks

## Abstract

Finite theta-mass lower bounds for the complete first-layer loss.

The loss is the existing ActualRecordHigherLayerResidual.completeFirstLayerLoss, summed over the union of the strict optimizer's prime support and the original integer's prime support. No selected tail, squarefree replacement, record error bound, prime number theorem, or RH assumption is used. Let X>4, m>=2, m.primeFactors=primesLE(Q), and 1<a<b. Write M=theta(b)-theta(a).

**Theorem 1.1 (Missing positive block).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.missing_block_theta_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.missing_block_theta_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Q<=a and b+1/2<X, then (X-b-1/2)*M/(X*(b+1/2)*log(b)) is at most the complete first-layer loss. Every block prime a<p<=b is absent from m. Mathlib's 2u/(u+2)<log(1+u), at u=1/p, gives raw margin >=1/(p+1/2)-1/X>=1/(b+1/2)-1/X>0. The library's exact positive-layer count interval and strictInteger_counts place that prime in the actual optimizer support. Its missing loss is therefore its raw margin.

**Theorem 1.2 (Occupied negative block).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.occupied_block_theta_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.occupied_block_theta_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If b<=Q and X<a, then (a-X)*M/(X*a*log(b)) is at most the same complete first-layer loss. Every a<p<=b divides m and has positive valuation. The tangent bound log(1+1/p)<=1/p and log(p)>=log(X) give negative raw margin at least 1/X-1/p>=1/X-1/a>0. Occupied loss dominates that quantity.

For both clauses the exact block is primesLE(floor(b)) minus primesLE(floor(a)), including b and excluding a even when an endpoint is prime. Its log sum is exactly M, and each log(p)<=log(b), hence M<=card(block)*log(b). Summing the strictly positive uniform margin and extending by nonnegative loss terms proves the result. The proof never divides by M or card(block), so empty blocks and zero theta mass remain covered. These are finite estimates only: they assert no global coercivity equivalence, first-layer asymptotic bound, or RH criterion. No literature novelty is claimed.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.missing_block_theta_lower_bound`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.occupied_block_theta_lower_bound`
- Dependency: [D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone](../../GoldenResource/FirstLayerMarginalAntitone.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualRecordHigherLayerResidual](ActualRecordHigherLayerResidual.md)
