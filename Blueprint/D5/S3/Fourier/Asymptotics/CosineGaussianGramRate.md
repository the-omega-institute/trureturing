# Gaussian Weighting of the Cosine-Integral Gram Product

## Abstract

Gaussian weighting approximates the cosine-integral Gram integral with an explicit inverse-radius error.

**Theorem 1.1 (An error bound for all positive scales and radii).**

$$\forall a \in \mathbb{R}, b \in \mathbb{R}, beta \in \mathbb{R}, R \in \mathbb{R},\; \left(\left(0 < a \land 0 < b\right) \land \left(0 < beta \land 0 < R\right)\right) \Rightarrow \left(\operatorname{Integrable}\left((z: \mathbb{R} \mapsto \operatorname{Ci}\left(a \cdot \left|z\right|\right) \cdot \operatorname{Ci}\left(b \cdot \left|z\right|\right) \cdot \operatorname{exp}\left(-beta \cdot \frac{z}{R}^{2}\right))\right) \land \left|\int_{\mathbb{R}} \operatorname{Ci}\left(a \cdot \left|z\right|\right) \cdot \operatorname{Ci}\left(b \cdot \left|z\right|\right) \cdot \operatorname{exp}\left(-beta \cdot \frac{z}{R}^{2}\right) dz-\frac{\pi}{\operatorname{max}\left(a, b\right)}\right| \le \frac{8 \cdot {beta+1}}{a \cdot b \cdot R}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineGaussianGramRate.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a, b, beta and R be arbitrary positive real numbers. The product Ci(a|z|)Ci(b|z|) multiplied by exp(-beta(z/R)^2) is Lebesgue integrable on the real line. Its integral differs from pi/max(a,b) by at most 8(beta+1)/(abR). Here Ci is the real cosine integral defined at positive x by sin(x)/x minus the integral of sin(t)/t^2 from x to infinity.`D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral`

The unweighted product is integrable and has integral pi/max(a,b). Since the Gaussian factor is continuous and lies between zero and one, multiplication by it preserves integrability.`D5/S3/Fourier/Asymptotics/CosineIntegralGram.result`

For every x>0, the sine-tail representation gives |Ci(x)|<=2/x: the first term has absolute value at most 1/x, and the integral of t^(-2) from x to infinity is 1/x. Consequently the absolute value of the product at z different from zero is at most 4/(abz^2).

For u>=0 the Gaussian decrement satisfies 0<=1-exp(-u)<=min(u,1). On the interval |z|<=R, the absolute error integrand is therefore at most 4beta/(abR^2), except at the null singleton zero. Outside that interval it is at most 4/(abz^2). The two integrated bounds are 8beta/(abR) and 8/(abR), respectively, yielding the stated estimate.

If a and b range over compact subsets of the positive real axis and beta remains bounded above, the displayed constant is uniform. Thus the approximation error is uniformly O(1/R). This statement concerns deterministic Lebesgue integrals.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineGaussianGramRate.result`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralGram.result`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral`
- Dependency: [D5/S3/Fourier/Asymptotics/CosineIntegralGram](CosineIntegralGram.md)
