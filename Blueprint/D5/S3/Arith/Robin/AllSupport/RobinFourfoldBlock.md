# Fourfold intervals for the weighted Robin tail

## Abstract

An eventual lower bound on a finite Robin block characterizes RH.

**Theorem 1.1 (Abel summation on a fourfold interval).**

Lean statement: `D5/S3/Arith/Robin/AllSupport/RobinFourfoldBlock.finite_robin_block_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/AllSupport/RobinFourfoldBlock.finite_robin_block_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The drop in the weighted Chebyshev theta tail between x and 4x equals the prime reciprocal sum over the right-closed interval with two Chebyshev boundary terms and an explicit smooth correction.

**Theorem 1.2 (RH and a finite prime-reciprocal inequality).**

Lean statement: `D5/S3/Arith/Robin/AllSupport/RobinFourfoldBlock.rh_iff_eventual_integer_fourfold_robin_block`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/AllSupport/RobinFourfoldBlock.rh_iff_eventual_integer_fourfold_robin_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH implies that the normalized block is eventually at least minus eleven tenths. Conversely, summing the block lower bound along the scales n, 4n, 16n and onward controls the full weighted tail. A unit-interval estimate transfers this control from integer endpoints to real endpoints for the weighted-tail converse.

## References

- Truth anchor: `D5/S3/Arith/Robin/AllSupport/RobinFourfoldBlock.finite_robin_block_identity`
- Truth anchor: `D5/S3/Arith/Robin/AllSupport/RobinFourfoldBlock.rh_iff_eventual_integer_fourfold_robin_block`
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](../ActualRobinClockCovariance.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope](../Analytic/RHSharpArithmeticEnvelope.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound](../../../Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.md)
- Dependency: [D5/S3/Weil/Mertens/RobinWeightedTailConverse](../../../Weil/Mertens/RobinWeightedTailConverse.md)
