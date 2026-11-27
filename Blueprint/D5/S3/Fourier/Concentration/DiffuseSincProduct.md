# Euclidean-Scale Bound for Diffuse Sinc Products

## Abstract

A reciprocal quadratic controls the finite sinc product under a dispersion condition.

Let A be a finite index set and c a family of real coefficients. Write S for the sum of the squares of c(j) over A, and suppose the sum of the fourth powers is at most S²/2. Here sinc(x)=sin(x)/x for nonzero x and sinc(0)=1.

**Theorem 1.1 (Reciprocal quadratic envelope).**

$$\prod_{j \in A}\left|\operatorname{sinc}(\operatorname{c}\left(j\right)t)\right| \le \frac{1}{1 + \frac{St^{2}}{15}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/DiffuseSincProduct.diffuse_sinc_product_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar bound is sinc(x)²(1+2x²/15)≤1. On 0≤x≤2, integrate cos(t)≤1−t²/5 to get sinc(x)≤1−x²/15. If a=x²/15, then (1−a)²(1+2a)=1−a²(3−2a)≤1. For x≥2, use |sin(x)|≤1 and 1+2x²/15≤x². Evenness extends the bound to all real x.

Set b(j)=2(c(j)t)²/15 and U equal to their sum. The product of 1+b(j) dominates 1+U+(U²−Σb(j)²)/2 by multiplying out the nonnegative terms. The diffuse hypothesis implies Σb(j)²≤U²/2. The lower bound is therefore at least (1+U/2)². Combine this with the scalar estimate multiplied over A and take the nonnegative square root.

The formula includes vanishing coefficients and an empty index set. For S>0 its right side is integrable on the real line with integral π√(15/S). The fourth-moment condition follows if every c(j)²≤S/2, and also holds for coefficients (3,2,2) with S=17. This is the characteristic function envelope for an independent uniform perturbation. Using it for interval probabilities requires a separate estimate passing from the characteristic function to the measure of a short interval.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/DiffuseSincProduct.diffuse_sinc_product_le`
