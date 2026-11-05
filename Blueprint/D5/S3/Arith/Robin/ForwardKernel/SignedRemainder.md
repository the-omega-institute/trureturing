# The signed remainder limit

## Abstract

The signed remainder limit.

**Theorem 1.1 (The signed remainder limit).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SignedRemainder.signed_remainder_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SignedRemainder.signed_remainder_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume alpha>=0 and an eventual bound |E(t)|<=C*t^alpha. For a>=3, sigma>alpha-7/10 and A>=0, suppose r has derivative dr on [a,infinity), dr is almost everywhere strongly measurable there, and the bounds |r(t)|<=A*t^(-sigma-7/10), |dr(t)|<=A*t^(-sigma-17/10) hold. Then sum(Lambda(n)*r(n),floor(a)<n<=floor(b))-integral_a^b r(t) dt tends to -E(a)*r(a)-integral_a^infinity E(t)*dr(t) dt. Finite Abel summation preserves all prime powers and the stated bounds send the final endpoint to zero.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SignedRemainder.signed_remainder_tendsto`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/RemainderContinuation](RemainderContinuation.md)
