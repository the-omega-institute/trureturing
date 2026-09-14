# Salem Integral Uniqueness

## Abstract

The original Salem integral equation has only the almost-everywhere zero bounded completed-measurable complex solution for every delta in (1/2,1) exactly when RH holds.

Volume is real Lebesgue measure, and mu is its restriction to (0,infinity). All displayed powers of positive t in the original integral are real powers included in the complex numbers. NullMeasurable means measurable on the completed sigma algebra of mu; it allows arbitrary representatives on null sets. The conclusion is mu-almost-everywhere equality.

**Definition 1.1 (The logarithmic kernel).**

$$\forall delta \in \mathbb{R},\; \forall u \in \mathbb{R},\; \operatorname{salemKernel}\left(delta, u\right) = \frac{\operatorname{exp}\left(delta\,u\right)}{\operatorname{exp}\left(\operatorname{exp}\left(u\right)\right)+1}$$

*Formalization.* `D5/S3/Weil/ZetaBridge/SalemIntegralUniqueness.salemKernel` (`✓ std3`).

*Citation.* Raphaël Salem (1953). *Sur une proposition équivalente à l’hypothèse de Riemann*. URL: <https://gallica.bnf.fr/ark:/12148/bpt6k3188h>.

*Commentary.*

This is Salem's kernel on page 1128, regarded as complex-valued. For delta > 0 it belongs to L1: the exponential Jacobian integrability equivalence transfers the existing Fermi Mellin integrability theorem at scale one. The Fourier convention exp(-2 pi i u xi) identifies its transform with the Mellin integral at delta - 2 pi i xi.

**Theorem 1.2 (Original integral in convolution coordinates).**

$$\forall delta \in \mathbb{R},\; \forall y \in \mathbb{R},\; \forall f \in \mathbb{R}\to\mathbb{C},\; \int_{0}^{\infty} \frac{t^{delta-1}\,\operatorname{f}\left(t\right)}{\operatorname{exp}\left(\operatorname{exp}\left(y\right)\,t\right)+1}\,dt = \operatorname{exp}\left(-delta\,y\right)\,\int_{\mathbb{R}} \operatorname{salemKernel}\left(delta, u\right)\,\operatorname{f}\left(\operatorname{exp}\left(u-y\right)\right)\,du$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/SalemIntegralUniqueness.salem_integral_eq_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Raphaël Salem (1953). *Sur une proposition équivalente à l’hypothèse de Riemann*. URL: <https://gallica.bnf.fr/ark:/12148/bpt6k3188h>.

*Commentary.*

Apply the positive-logarithmic Mellin dilation identity, then translate by y. The exponent contributes the factor exp(-delta y). This equality holds for arbitrary delta, y and f using totalized Bochner integrals; it does not assert convergence by itself.

For delta > 0 and bounded NullMeasurable f, positive-scale Fermi Mellin integrability and bounded multiplication prove genuine integrability of the original integrand. Kernel integrability and the transported bound prove genuine convolution integrability. The completed measure agrees on every set and has the same AE filter. Trimming it to the original sigma algebra and applying the Bochner integral trim theorem identifies its integral with the one displayed here.

**Theorem 1.3 (Full bounded measurable uniqueness iff RH).**

$$\operatorname{RiemannHypothesis}\left(\right) \Leftrightarrow \left(\forall delta \in \mathbb{R},\; \frac{1}{2} < delta \Rightarrow \left(delta < 1 \Rightarrow \left(\forall f \in \mathbb{R}\to\mathbb{C},\; \operatorname{NullMeasurable}\left(f, \operatorname{restrict}\left(\operatorname{volume}\left(\right), \operatorname{Ioi}\left(0\right)\right)\right) \Rightarrow \left(\left(\exists B \in \mathbb{R},\; 0 \le B \land \left(\forall t \in \mathbb{R},\; 0 < t \Rightarrow \Vert\operatorname{f}\left(t\right)\Vert \le B\right)\right) \Rightarrow \left(\left(\forall x \in \mathbb{R},\; 0 < x \Rightarrow \int_{0}^{\infty} \frac{t^{delta-1}\,\operatorname{f}\left(t\right)}{\operatorname{exp}\left(x\,t\right)+1}\,dt = 0\right) \Rightarrow \forall_{\mathrm{ae} \operatorname{restrict}\left(\operatorname{volume}\left(\right), \operatorname{Ioi}\left(0\right)\right)} t\in\mathbb{R}, \operatorname{f}\left(t\right)=0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/SalemIntegralUniqueness.salem_bounded_measurable_uniqueness_iff_rh` (`✓ std3`). ∎

*Citation.* Raphaël Salem (1953). *Sur une proposition équivalente à l’hypothèse de Riemann*. URL: <https://gallica.bnf.fr/ark:/12148/bpt6k3188h>.

*Commentary.*

The quantifiers include every real delta strictly between 1/2 and 1, every complex function on the real line whose restriction to the positive half-line is completed-measurable, and one finite nonnegative real bound B valid at every positive t. The equation holds for every positive scale x. Values at nonpositive t have no effect. No integrability or regularity of f is assumed.

For RH implies uniqueness, put g(v) = f(exp(-v)). The maps exp(-v) and -log(t) preserve null sets in both directions, using the differentiability of their inverses on the appropriate domains. Complex separability converts NullMeasurable to AE strong measurability. Thus g meets the measurability and bound required by the existing bounded convolution cancellation theorem.

The existing Fermi Mellin criterion gives a nowhere-zero spectrum. Gamma(s)(1-2^(1-s))zeta(s) is holomorphic on 0 < Re(s) < 1. Real scalar restriction and composition with s = delta - 2 pi i xi give its real infinite differentiability. Convolution cancellation makes g zero AE; inverse logarithmic transport returns the conclusion on the original positive half-line.

For the converse, a Mellin zero at delta + i gamma supplies f(t) = exp(i gamma log t). This measurable function has norm one, so it cannot vanish AE on the positive-measure interval (1,2]. Its original integrals are integrable, and positive Mellin scaling multiplies the zero at one by x^(-delta-i gamma). Uniqueness excludes every such zero; the existing Mellin nonvanishing equivalence yields RH.

Salem's 1953 note gives the bounded-equation and Wiener-transform argument. The explicit complex, completed-measure and AE conventions, and the all-delta right-half-strip formulation, are the modern original-integral statement explained in the Library note. FermiMellin and SmoothConvolutionUniqueness provide the separately attributed implementation results.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/SalemIntegralUniqueness.salemKernel`
- Truth anchor: `D5/S3/Weil/ZetaBridge/SalemIntegralUniqueness.salem_bounded_measurable_uniqueness_iff_rh`
- Truth anchor: `D5/S3/Weil/ZetaBridge/SalemIntegralUniqueness.salem_integral_eq_convolution`
- Dependency: [D5/S3/Analytic/Dilation/MellinDilationFlow](../../Analytic/Dilation/MellinDilationFlow.md)
- Dependency: [D5/S3/Fourier/SmoothConvolutionUniqueness](../../Fourier/SmoothConvolutionUniqueness.md)
- Dependency: [D5/S3/Weil/ZetaBridge/FermiMellin](FermiMellin.md)
