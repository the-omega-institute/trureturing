# The Cosine-Integral Gram Integral

## Abstract

Positive dilations of the real cosine-integral tail have an absolutely integrable product and an exact Gram integral.

**Theorem 1.1 (All positive scales, including equal scales).**

$$\forall a \in \mathbb{R}, b \in \mathbb{R},\; \left(0 < a \land 0 < b\right) \Rightarrow \left(\operatorname{Integrable}\left((z: \mathbb{R} \mapsto \operatorname{Ci}\left(a \cdot \left|z\right|\right) \cdot \operatorname{Ci}\left(b \cdot \left|z\right|\right))\right) \land \int_{\mathbb{R}} \operatorname{Ci}\left(a \cdot \left|z\right|\right) \cdot \operatorname{Ci}\left(b \cdot \left|z\right|\right) dz = \frac{\pi}{\operatorname{max}\left(a, b\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineIntegralGram.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of positive real numbers a and b, the product Ci(a|z|)Ci(b|z|) is Lebesgue integrable on the real line and its integral is pi/max(a,b). In particular, the square at scale a has integral pi/a. Ci is the existing real cosine integral, defined for positive x as sin(x)/x minus the absolutely convergent integral of sin(t)/t^2 from x to infinity.`D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral`

On the positive half-line set S(x)=sinc(x) and T(x)=Ci(x)-S(x). The sine-tail representation and the fundamental theorem of calculus give T'(x)=S(x)/x. Consequently B(x)=x T(ax)T(bx) has derivative Ci(ax)Ci(bx)-S(ax)S(bx).

The tail is bounded by 1/x. Near zero, the normalized finite cosine-sum estimate at N=1 gives |Ci(x)|<=1+2K+|log(x)| for one K>0 and 0<x<=1. Thus sqrt(x)T(x) tends to zero. These estimates show that B tends to zero at both endpoints of the positive half-line.`D5/S3/Fourier/Asymptotics/CosineNormalizedRemainder.result`

Add the integral of S(at)S(bt) from zero to x to B(x), obtaining a primitive P with derivative Ci(ax)Ci(bx). For a=b this derivative is nonnegative. The finite limit of P at infinity and continuity at zero therefore establish square integrability by the nonnegative form of the fundamental theorem of calculus. The L2 product inequality then establishes integrability for arbitrary a and b, allowing the same primitive to transfer the integral to the sinc product.

The existing integral of (sin(x)/x)^2 is pi. Scaling gives the integral of (sin(cx)/x)^2 as pi|c|, with c=0 treated directly. Put p=(a+b)/2 and q=(a-b)/2. The sine-product identity expresses S(ax)S(bx), away from zero, as the difference of the squared sine quotients at p and q divided by ab. Its integral is therefore pi(p-|q|)/(ab)=pi/max(a,b). Reflection transfers the positive half-line calculation to the real line; the singleton at zero has Lebesgue measure zero.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralGram.result`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineNormalizedRemainder.result`
- Dependency: [D5/S3/Fourier/Asymptotics/CosineNormalizedRemainder](CosineNormalizedRemainder.md)
- Dependency: [D5/S3/TotalVariation/Asymptotics/StatLeanFourierCore](../../TotalVariation/Asymptotics/StatLeanFourierCore.md)
