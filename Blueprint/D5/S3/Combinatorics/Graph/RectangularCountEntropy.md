# Rectangular subadditivity and square entropy

## Abstract

Symmetric rectangular subadditivity implies a full square-area limit.

**Theorem 1.1 (A square limit from fixed-width Fekete limits).**

Lean statement: `D5/S3/Combinatorics/Graph/RectangularCountEntropy.square_log_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RectangularCountEntropy.square_log_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f map pairs of natural numbers to real numbers, let L be nonnegative, assume f(r,c)=f(c,r), assume subadditivity in r for each c, and assume 0<=f(r,c)<=r*c*L for every rectangle. Then there exists a nonnegative real s such that f(n,n)/n squared converges to s through all natural n. Pinned Mathlib Subadditive.tendsto_lim supplies each fixed-width limit g(c). The square limit is the infimum of g(k)/k over positive k. A cut into width-k strips and a remainder bounds the diagonal above by (f(n,k)/n)/k+k*L/n; Fekete's infimum bound supplies the lower bound. No diagonal convergence, periodic-boundary relation or two-dimensional entropy conclusion is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RectangularCountEntropy.square_log_limit`
