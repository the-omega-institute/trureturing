# Coupled cyclic moment matrices

## Abstract

A growing front window and a fixed rear window admit an invertible joint moment fit.

Let n run through the natural numbers and fix a finite set S of real rear offsets r. At mesh h use u=nh. On the integer front window from −n to n, use x=j/n, F=(1+cos(xu))/2, X=sin²(xu)/u², and W=1−F. At u=0, X=x². At each rear offset r put W=(1+cos(rh))/2, F=1−W, and X=r² sinc²(rh)/n². For positive n and nonzero h the rear feature is sin²(rh)/(nh)². The coefficient row is (F/n,X/n,W/n³) and the moment row is (F,X,n³W²). The coupled matrix M is the sum of the outer products of the moment and coefficient rows, over both windows, for positive n. Assume n³(nh)⁴→0. Since n≥1 eventually, this implies nh→0 and h→0.

**Theorem 1.1 (Limit of the three scaled moment rows).**

$$\operatorname{Limit}\left(\operatorname{M}\left(S, n, \operatorname{h}\left(n\right)\right)\right) = \operatorname{MatrixThree}\left(2, \frac{2}{3}, 0, \frac{2}{3}, \frac{2}{5}, 0, 0, \operatorname{RearSquareSum}\left(S\right), \operatorname{Card}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingCoupledFit.coupledMatrix_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper left front block converges to the two-feature lattice matrix. On the front, W≤u²/4 and F,X∈[0,1]. Hence the mixed upper column is bounded by 3u²/(4n²), the mixed lower row by 3n³u⁴/16, and the final entry by 3nu⁶/64. Each tends to zero. At a fixed rear offset, the scaled moment r² sinc²(rh) tends to r² and W tends to one. Since n²F≤r²(nh)²/4, the rear contribution to the first column also vanishes.

**Theorem 1.2 (Eventual unique fit to arbitrary three moments).**

$$\operatorname{EventuallyUnique}\left(n, a, \operatorname{Q}\left(n, a\right) = \operatorname{b}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingCoupledFit.coupledFit_eventually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose additionally that S is nonempty and b(n) is any sequence of real three-vectors. For a coefficient vector a the readout Q(n,a) is the sum, over both windows, of the moment row multiplied by the dot product of the coefficient row with a. The limiting matrix has determinant 16|S|/45, which is positive. Continuity of the determinant makes the finite matrices invertible eventually. For positive n the readout is exactly M(n)a, so inverse multiplication supplies the unique coefficient vector for each prescribed moment target. The coefficient fit permits signed weights. Positivity on the proposed cyclic support requires additional boundary estimates.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingCoupledFit.coupledFit_eventually`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingCoupledFit.coupledMatrix_tendsto`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicGrowingFrontFit](CyclicGrowingFrontFit.md)
