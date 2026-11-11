# Weighted collision error bounds

## Abstract

Quadratic reduction separates distinct-shift products from sparse collision errors.

**Theorem 1.1 (The weighted collision error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionErrorBounds.collision_error_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionErrorBounds.collision_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real endpoint cap M at least one there is a nonnegative constant C. For N at least two, integer H at least one with MH at most N, a weight w with BVBound(w,B), k equal to two, three or four, and any admissible family of k intervals in [0,M], the weighted discrete mixed moment differs from the sum of its tuple reductions at log n by at most C B times the sum of sqrt(N) H^(k-1) (log N)^(k+1) and H^k (log N)^(k-1). The first term comes from proper prime powers, counted using their square-root bound. A quadratic defect contributes only when its shift is repeated, leaving at most k-1 free shifts. The quadratic diagonal, five cubic and fifteen fourth-order equality patterns bound this repetition sum. Outside those exceptions the logarithm-shift bound controls the defect by MH/N times a logarithmic factor. The estimate is uniform in all interval endpoints and in the weight. Together with the common polynomial expansion of reducedAt and reducedTuple, it supplies the collision step of the weighted arithmetic transfer to Phi.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionErrorBounds.collision_error_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions](PrimePowerExceptions.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCollisionReduction](QuadraticCollisionReduction.md)
