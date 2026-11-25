# Uniform finite-window localization of the Fejer moment

## Abstract

The positive triangular spectral representation bounds the relative far-time contribution of the Fejer moment.

For a finite family of real frequencies g and nonnegative weights w, fix a natural degree p and let F(t)=|S(t)|^(2p), where S is the weighted complex Fourier score. Given eta>0, let M be the whole-line integral of K_eta F, where K_eta is the angular Fejer kernel. For R with eta R>=1 write I(R) for the integral of K_eta F over [-R,R].

**Theorem 1.1 (Relative tail bound).**

$$M - \operatorname{I}\left(R\right) \le \frac{64}{eta \cdot R} \cdot M$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FejerRelativeLocalization.relative_fejer_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The triangular Fourier identity has nonnegative occupation-pair coefficients. Increasing the resolution can only increase the triangular weight of every frequency difference, hence M_b<=M_eta whenever 0<b<=eta. For a radius T>=1/eta, set b=1/T. On [-T,T] the kernel K_b is at least 1/(8 pi T), so the integral of F on this interval is at most 8 pi T M. The quadratic Fejer kernel upper bound then bounds the increment I(2r)-I(r) by 32 M/(eta r) when r>=1/eta. Summing over the dyadic radii from R to 2^n R gives an error at most 64 M/(eta R) times 1-2^(-n). Integrability allows the upper radius to tend to infinity.

With a moving finite spectrum, weights, degree and resolution, any radius R for which eta R tends to infinity makes the far-time error relatively negligible, including the cases of zero or repeated frequencies. Nonnegative occupation-pair coefficients are essential to the scale comparison. Arithmetic estimates on the intermediate time range between a central Gaussian window and the distant cutoff remain necessary for an absolute whole-line asymptotic.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FejerRelativeLocalization.relative_fejer_truncation`
- Dependency: [D5/S3/Fourier/Concentration/FejerCollisionVariance](FejerCollisionVariance.md)
