# Continuous macroscopic weights

## Abstract

Uniform interval cancellation extends to continuous weights when absolute mass stays bounded.

**Theorem 1.1 (Lifting interval cancellation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightApproximation.continuous_weight_lifting`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightApproximation.continuous_weight_lifting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f(X,i,u) be eventually integrable on [1,2], with the integrals of its absolute value bounded by one constant uniformly in i. Suppose the integral over every subinterval tends to zero uniformly in i and in both endpoints. For every real continuous weight phi on [1,2], the integrals of phi(u)*f(X,i,u) tend to zero uniformly in i.

Uniform continuity provides a fixed partition into equal blocks on which phi differs little from its left endpoint value. The sum of the errors is at most that oscillation times the total absolute mass. The finite sum with the frozen weights tends to zero by interval cancellation. The partition is chosen before X. For linear averages, a uniform second-moment bound controls absolute mass by Cauchy–Schwarz; for bilinear averages, apply Cauchy–Schwarz to the two factors. A nonzero limiting density can be subtracted before applying this result.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightApproximation.continuous_weight_lifting`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells](MovingLengthCells.md)
