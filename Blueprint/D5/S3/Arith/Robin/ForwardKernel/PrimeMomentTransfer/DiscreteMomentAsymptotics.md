# Discrete moment asymptotic inputs

## Abstract

The discrete moment stage consumes the weighted arithmetic transfer and formal interval bounds.

**Theorem 1.1 (Arithmetic and formal moment envelopes).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteMomentAsymptotics.discrete_moment_asymptotic_inputs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteMomentAsymptotics.discrete_moment_asymptotic_inputs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume zero less than alpha less than beta less than one, normalized singular-series values on the empty set and singletons, the mean-square correlation bound through natural order q and interval correlation estimates. For every endpoint window M>=1 and positive epsilon, weighted discrete moments of orders k in {2,3,4} with k<=q have a uniform arithmetic transfer error of size C B N to the power one half plus epsilon times H to the moment order. The formal cubic and fourth envelopes share a nonnegative modulus, antitone from two and tending to zero, uniformly for lengths in the prescribed power band and logarithms in the dyadic window.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteMomentAsymptotics.discrete_moment_asymptotic_inputs`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds](FormalIntervalMomentBounds.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer](WeightedArithmeticTransfer.md)
