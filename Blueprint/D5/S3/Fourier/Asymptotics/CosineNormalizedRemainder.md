# A Uniform Cosine-Sum Remainder

## Abstract

A uniform finite cosine-sum error estimate uses the actual cosine-integral tail and its Euler constant normalization.

**Theorem 1.1 (One error constant for all positive frequencies and truncations).**

$$\exists C \in \mathbb{R},\; 0 < C \land \left(\forall \theta \in \mathbb{R}, \left(0 < \theta \land \theta \le 1\right) \Rightarrow \left(\forall N \in \mathbb{N},\; 1 \le N \Rightarrow \left|\sum_{k=1}^{N} \frac{\operatorname{cos}\left(k \cdot \theta\right)}{k} - \left(-\operatorname{log}\left(\theta\right) + \operatorname{Ci}\left(N \cdot \theta\right)\right)\right| \le C \cdot \left(\frac{1}{N} + \theta \cdot \left(1 + \operatorname{max}\left(0, \operatorname{log}\left(N \cdot \theta\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineNormalizedRemainder.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one positive real constant C, independent of both theta and N. For every real frequency 0<theta<=1 and every integer N>=1, the sum from k=1 to N differs from -log(theta)+Ci(N theta) by at most the displayed error. Here log is the natural logarithm and max(0,log(x)) is its positive part. The proof takes C=6.

The function Ci is the real cosine integral defined by the absolutely convergent sine tail below for x>0. Integration by parts identifies this expression with the negative improper integral of cos(t)/t from x to infinity.`D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral`

$$
\forall x \in \mathbb{R},\; 0 < x \Rightarrow \operatorname{Ci}\left(x\right) = \frac{\operatorname{sin}\left(x\right)}{x} - \int_{x}^{\infty} \frac{\operatorname{sin}\left(t\right)}{t^{2}} dt
$$

Write q(t)=(cos(t)-1)/t, taking q(0)=0, and let Q(x) be its integral from 0 to x. First estimate g(t)=(cos(theta t)-1)/t, also extended by zero at the origin. The sinc identity makes g continuous there. For t>0, elementary trigonometric bounds give |g'(t)|<=6 theta^2/(1+theta t), while |g(t)|<=theta. The first Euler--Maclaurin formula, the bound 1/2 on its periodic Bernoulli factor, and the integral over the first unit interval give the following quadrature estimate.

$$
\left(\forall \theta \in \mathbb{R}, \left(0 < \theta \land \theta \le 1\right) \Rightarrow \left(\forall N \in \mathbb{N},\; 1 \le N \Rightarrow \left|\sum_{k=1}^{N} \frac{\operatorname{cos}\left(\theta \cdot k\right) - 1}{k} - \int_{0}^{N} \frac{\operatorname{cos}\left(\theta \cdot t\right) - 1}{t} dt\right| \le 5 \cdot \theta \cdot \left(1 + \operatorname{max}\left(0, \operatorname{log}\left(N \cdot \theta\right)\right)\right)\right)\right)
$$

After the change of variables u=theta t, add the harmonic sum. Its difference from log(N)+gamma is positive and at most 1/(2N), where gamma is Euler's constant. This gives the desired error around gamma+log(N)+Q(N theta). It remains to identify this center with the actual cosine integral.

Integration by parts in the sine tail shows that Ci(x)=Ci(1)+log(x)+Q(x)-Q(1) for x>0. The constant is determined analytically: for a>0, differentiation under an integrable exponential majorant evaluates the damped q integral.

$$
\forall a \in \mathbb{R},\; 0 < a \Rightarrow \int_{0}^{\infty} \operatorname{exp}\left(-\left(a \cdot t\right)\right) \cdot \frac{\operatorname{cos}\left(t\right) - 1}{t} dt = \operatorname{log}\left(a\right) - \frac{\operatorname{log}\left(a^{2} + 1\right)}{2}
$$

The derivative uses the exponential cosine integral a/(a^2+1); the integration constant is fixed by the limit as a tends to infinity. Scaling the logarithmic Gamma integral gives a times the integral of exp(-a t) log(t) equal to -gamma-log(a). Integration by parts also gives a times the Laplace integral of Q equal to the Laplace integral of q. Combining these identities produces the next equality.

$$
\forall a \in \mathbb{R},\; 0 < a \Rightarrow a \cdot \int_{0}^{\infty} \operatorname{exp}\left(-\left(a \cdot t\right)\right) \cdot \operatorname{Ci}\left(t\right) dt = \operatorname{Ci}\left(1\right) - \operatorname{Q}\left(1\right) - \gamma - \frac{\operatorname{log}\left(a^{2} + 1\right)}{2}
$$

The positive-lattice square bound for Ci implies |Ci(t)|<=sqrt(K)/sqrt(t) for some K>0 and all t>0. Consequently the absolute value of the left side is at most sqrt(K) sqrt(a) Gamma(1/2), which tends to zero as a decreases to zero. The logarithmic term on the right also tends to zero. Thus Ci(1)-Q(1)=gamma, and the normalization follows.`D5/S3/Fourier/Asymptotics/CosineIntegralLattice.result`

$$
\forall x \in \mathbb{R},\; 0 < x \Rightarrow \operatorname{Ci}\left(x\right) = \gamma + \operatorname{log}\left(x\right) + \int_{0}^{x} \frac{\operatorname{cos}\left(t\right) - 1}{t} dt
$$

Substitute x=N theta and use log(N theta)=log(N)+log(theta). The quadrature error and the harmonic remainder sum to at most 5 theta(1+max(0,log(N theta)))+1/(2N), which is bounded by the stated expression with C=6. The assertion concerns positive theta, including arbitrarily small positive frequencies, with no coupling condition between theta and N.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralLattice.result`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineNormalizedRemainder.result`
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](../../Arith/GoldenResource/RobinRationalBasis.md)
- Dependency: [D5/S3/Fourier/Asymptotics/CosineIntegralLattice](CosineIntegralLattice.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](../../Weil/ZetaGamma/ArchimedeanJumpDecomposition.md)
