# Minimum squared mass with one lower moment bound

## Abstract

A normalized positive part attains a prescribed real moment at minimum squared mass.

**Theorem 1.1 (Exact optimizer for one real lower moment bound).**

$$\begin{aligned}&\frac{\sum_{i}c_{i}}{|I|} \le a \le C,\quad \exists t \ge0,\\&u_{i}=\max(0,1-t(C-c_{i})),\quad v_{i}=\frac{u_{i}}{\sum_{j}u_{j}},\\&v_{i} \ge0,\quad \sum_{i}v_{i}=1,\quad \sum_{i}v_{i}c_{i}=a,\\&\sum_{i}(w_{i}-v_{i})^{2} \le \sum_{i}\left(w_{i}\right)^{2}-\sum_{i}\left(v_{i}\right)^{2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/ClippedMomentWeights.exists_clipped_moment_minimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The indices form a finite set I. The readout c is real, C is its attained maximum, and a lies between the mean of c under the uniform law and C. All sums range over I. The last line holds for every nonnegative w with sum one and moment at least a.

At t = 0 the weights are uniform. Every index attaining the maximum has raw weight one for every t, so the normalization stays positive. At one plus the sum of the reciprocals of the positive gaps C − cᵢ, every submaximal index has weight zero. The normalized moment is continuous between these endpoints, so it attains a at a finite t.

Write the raw affine weights as 1 − t(C − cᵢ). Their inner product with w − v is nonnegative because the masses agree and the moment of w is at least that of v. Taking positive parts can only increase this inner product. At each clipped index v vanishes and w is nonnegative. After normalization, expand the squared norm around v. The lower bound by the squared distance forces uniqueness.

For cyclic Fourier weights, cᵢ can be the real part of a character at a single spatial residue. The resulting squared mass is the minimum with this one constraint. A whole spatial band imposes further joint constraints.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/ClippedMomentWeights.exists_clipped_moment_minimizer`
