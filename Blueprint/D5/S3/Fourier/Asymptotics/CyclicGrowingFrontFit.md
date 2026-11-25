# Moment matrices on growing cyclic windows

## Abstract

The front moment matrix admits a uniform mesh error and an exact lattice reference solution.

**Theorem 1.1 (Uniform error in each matrix entry).**

$$0 < n, \operatorname{Abs}\left(\operatorname{G}\left(n, u, i, j\right) - \operatorname{G}\left(n, 0, i, j\right)\right) \le 2 \cdot u^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingFrontFit.frontGram_sub_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the integer window from −n to n, use x=j/n and the scaled mesh u. The two features are (1+cos(xu))/2 and sin²(xu)/u². At u=0 they are 1 and x². The matrix G sums their pair products and divides by n. Both features lie in [0,1]. The cubic sine remainder bounds the error in the second feature by u²/3, uniformly in the window. The first feature has error at most u²/4. The product difference and the exact cardinality 2n+1 give the entrywise bound.

**Theorem 1.2 (Limit along any vanishing scaled mesh).**

$$\operatorname{Limit}\left(\operatorname{u}\left(n\right)\right) = 0 \Rightarrow \operatorname{Limit}\left(\operatorname{G}\left(n, \operatorname{u}\left(n\right)\right)\right) = \operatorname{SymmetricTwoByTwo}\left(2, \frac{2}{3}, \frac{2}{5}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingFrontFit.frontGram_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero mesh the normalized sums of 1, x², and x⁴ give the three matrix entries. The uniform bound makes the difference tend to zero for every real sequence u tending to zero.

**Theorem 1.3 (The reference fit at the interior lattice budget).**

$$0 < n, \operatorname{G}\left(n, 0\right) \cdot \operatorname{Column}\left(\frac{n \cdot t}{Z}, \frac{0 - n^{3}}{Z}\right) = \operatorname{Column}\left(1, \frac{m}{n^{2}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingFrontFit.frontGram_reference_fit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive integer n, put m=n(n+1)/5 and t=n(n+1)−1/2. The normalizer Z is the sum of t−j² over the window. The stated matrix equation certifies mass one and normalized second moment m/n² for the lattice parabola. Using the exact finite reference retains the boundary margin lost in the limiting parabola.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingFrontFit.frontGram_reference_fit`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingFrontFit.frontGram_sub_le`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingFrontFit.frontGram_tendsto`
- Dependency: [D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation](LatticeSquareMomentActivation.md)
