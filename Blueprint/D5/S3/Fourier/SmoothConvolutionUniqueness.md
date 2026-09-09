# Smooth Convolution Uniqueness

## Abstract

A smooth nowhere-zero kernel spectrum forces bounded complex convolution solutions to vanish almost everywhere.

**Theorem 1.1 (Bounded convolution cancellation with a smooth nonvanishing spectrum).**

$$\forall k \in \mathbb{R}\to\mathbb{C}, g \in \mathbb{R}\to\mathbb{C},\; \left(\left(\left(\left(\left(\operatorname{Integrable}\left(k, \operatorname{volume}\left(\right)\right) \land \operatorname{ContDiff}\left(\mathbb{R}, \infty, \operatorname{FT}\left(k\right)\right)\right) \land \left(\forall xi \in \mathbb{R},\; \operatorname{FT}\left(k, xi\right) \ne 0\right)\right) \land \operatorname{AEStronglyMeasurable}\left(g, \operatorname{volume}\left(\right)\right)\right) \land \left(\exists M \in \mathbb{R},\; 0 \le M \land \left(\forall y \in \mathbb{R},\; \Vert\operatorname{g}\left(y\right)\Vert \le M\right)\right)\right) \land \left(\forall y \in \mathbb{R},\; \int_{\mathbb{R}} \operatorname{k}\left(u\right)\,\operatorname{g}\left(y-u\right)\,\mathrm{d}u = 0\right)\right) \Rightarrow \forall_{\mathrm{ae} \operatorname{volume}\left(\right)} y\in\mathbb{R}, \operatorname{g}\left(y\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/SmoothConvolutionUniqueness.ae_eq_zero_of_smooth_fourier_convolution_eq_zero` (`✓ std3`). ∎

*Citation.* Robert Fulsche, Franz Luef, Reinhard F. Werner (2025). *Wiener's Tauberian theorem in classical and quantum harmonic analysis*. URL: <https://arxiv.org/abs/2405.08678v2>.

*Commentary.*

All variables range over the real line unless a complex codomain is shown. Volume denotes Lebesgue measure. FT is the Fourier transform with phase exp(-2 pi i u xi). The conclusion holds for volume-almost every y. AEStronglyMeasurable means almost-everywhere strong measurability. The bound uses one real constant M, nonnegative and valid at every y.

This is a smooth-spectrum specialization of the bounded cancellation corollary of Wiener's approximation theorem. The source states density of translates in L1, and its complex dual pairing has no conjugation. The functional h mapped to the integral of h(u)g(-u) annihilates every translate of k. Density makes the functional zero; duality and measure-preserving reflection give g = 0 almost everywhere. The source angular frequency is 2 pi times xi. Its general theorem does not require the additional smoothness hypothesis.

For the smooth-spectrum argument, divide a compact smooth frequency test by FT(k). The quotient remains smooth with compact support, and its inverse Fourier transform is a Schwartz function h whose convolution with k equals the inverse transform of the test. An integrable product majorant permits Fubini with bounded g, so this factor also annihilates g.

A compact frequency bump equal to one at zero has inverse transform of integral one. Scaling, translation continuity in L1 and dominated convergence approximate each compact smooth spatial test in L1 by inverse transforms of compact smooth frequency tests. The bounded reflected pairing passes to the limit. Local integrability and separation by compact smooth tests yield the almost-everywhere conclusion.

## References

- Truth anchor: `D5/S3/Fourier/SmoothConvolutionUniqueness.ae_eq_zero_of_smooth_fourier_convolution_eq_zero`
