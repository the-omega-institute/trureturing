# Weighted integral tools

## Abstract

Uniform integration bounds for bounded variation weights.

**Theorem 1.1 (Supremum bound for a BV weight).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools.bv_sup_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools.bv_sup_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the supremum bound plus the total variation of a supported weight is at most B, then its absolute value is at most B at every real argument.

**Theorem 1.2 (A uniform weighted integral bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools.weighted_integral_uniform_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools.weighted_integral_uniform_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative N, B and E, if the absolute values of w(x/N) and f(x) on [N,2N] are at most B and E respectively, then the absolute value of their product integral is at most N B E.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools.bv_sup_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools.weighted_integral_uniform_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer](WeightedArithmeticTransfer.md)
