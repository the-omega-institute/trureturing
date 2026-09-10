# Fermi Mellin Integral

## Abstract

The Fermi Mellin integral on the positive half-plane and the Salem RH criterion.

**Theorem 1.1 (Positive-scale integrability).**

$$\forall x \in \mathbb{R},\; 0 < x \Rightarrow \left(\forall s \in \mathbb{C},\; 0 < \operatorname{Re}\left(s\right) \Rightarrow \operatorname{IntegrableOn}\left(t\mapsto\frac{t^{s-1}}{\operatorname{exp}\left(x\,t\right)+1}, \operatorname{Ioi}\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Sanftenberg (2026). *Fermi Mellin proof slice from RiemannGaussian*. URL: <https://github.com/dbsanfte/RiemannGaussian/tree/e00f5c558703e7fda181988142e143bb27c1d2c7>.

*Commentary.*

The exponentially dominated finite-prefix kernel gives convergence for every positive scale and every complex exponent with positive real part.

**Theorem 1.2 (Value away from one).**

$$\forall x \in \mathbb{R},\; 0 < x \Rightarrow \left(\forall s \in \mathbb{C},\; 0 < \operatorname{Re}\left(s\right) \Rightarrow \left(s \ne 1 \Rightarrow \int_{0}^{\infty} \frac{t^{s-1}}{\operatorname{exp}\left(x\,t\right)+1}\,dt = x^{-s}\,\operatorname{Gamma}\left(s\right)\,(1-2^{1-s})\,\operatorname{riemannZeta}\left(s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_eq_of_ne_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Sanftenberg (2026). *Fermi Mellin proof slice from RiemannGaussian*. URL: <https://github.com/dbsanfte/RiemannGaussian/tree/e00f5c558703e7fda181988142e143bb27c1d2c7>.

*Commentary.*

The paired finite integrals meet the public frozen natural alternating-sum limit. Positive scaling preserves the entire domain, including real part one.

**Theorem 1.3 (Removable product limit).**

$$\forall x \in \mathbb{R},\; 0 < x \Rightarrow \lim_{s\in\mathbb{C}, s\to1, s\neq1} x^{-s}\,\operatorname{Gamma}\left(s\right)\,(1-2^{1-s})\,\operatorname{riemannZeta}\left(s\right) = \frac{\operatorname{log}\left(2\right)}{x}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_product_tendsto_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Sanftenberg (2026). *Fermi Mellin proof slice from RiemannGaussian*. URL: <https://github.com/dbsanfte/RiemannGaussian/tree/e00f5c558703e7fda181988142e143bb27c1d2c7>.

*Commentary.*

The dyadic derivative quotient cancels the zeta residue. Gamma and scale are continuous at one; equality of the products is used only off one.

**Theorem 1.4 (Actual integral at one).**

$$\forall x \in \mathbb{R},\; 0 < x \Rightarrow \int_{0}^{\infty} \frac{t^{1-1}}{\operatorname{exp}\left(x\,t\right)+1}\,dt = \frac{\operatorname{log}\left(2\right)}{x}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_at_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Sanftenberg (2026). *Fermi Mellin proof slice from RiemannGaussian*. URL: <https://github.com/dbsanfte/RiemannGaussian/tree/e00f5c558703e7fda181988142e143bb27c1d2c7>.

*Commentary.*

Exponential decay and boundedness at zero make the actual Mellin transform continuous at one. Its value is identified by the punctured product limit.

**Theorem 1.5 (Full-domain identity).**

$$\forall x \in \mathbb{R},\; 0 < x \Rightarrow \left(\forall s \in \mathbb{C},\; 0 < \operatorname{Re}\left(s\right) \Rightarrow \left(\operatorname{IntegrableOn}\left(t\mapsto\frac{t^{s-1}}{\operatorname{exp}\left(x\,t\right)+1}, \operatorname{Ioi}\left(0\right)\right) \land \int_{0}^{\infty} \frac{t^{s-1}}{\operatorname{exp}\left(x\,t\right)+1}\,dt = \operatorname{ite}\left(s = 1, \frac{\operatorname{log}\left(2\right)}{x}, x^{-s}\,\operatorname{Gamma}\left(s\right)\,(1-2^{1-s})\,\operatorname{riemannZeta}\left(s\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Sanftenberg (2026). *Fermi Mellin proof slice from RiemannGaussian*. URL: <https://github.com/dbsanfte/RiemannGaussian/tree/e00f5c558703e7fda181988142e143bb27c1d2c7>.

*Commentary.*

The endpoint branch is a proved integral value. The raw totalized Gamma-dyadic-zeta product at one is not substituted for that value.

**Theorem 1.6 (Pointwise strip nonvanishing).**

$$\forall s \in \mathbb{C},\; \left(\frac{1}{2} < \operatorname{Re}\left(s\right) \land \operatorname{Re}\left(s\right) < 1\right) \Rightarrow \left(\int_{0}^{\infty} \frac{t^{s-1}}{\operatorname{exp}\left(1\,t\right)+1}\,dt \ne 0 \Leftrightarrow \operatorname{riemannZeta}\left(s\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_nonzero_iff_zeta_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Sanftenberg (2026). *Fermi Mellin proof slice from RiemannGaussian*. URL: <https://github.com/dbsanfte/RiemannGaussian/tree/e00f5c558703e7fda181988142e143bb27c1d2c7>.

*Commentary.*

Gamma has no zero for positive real part. The dyadic factor can vanish only at real part one, outside this open strip.

**Theorem 1.7 (Salem criterion iff RH).**

$$\left(\forall delta \in \mathbb{R},\; \frac{1}{2} < delta \Rightarrow \left(delta < 1 \Rightarrow \left(\forall gamma \in \mathbb{R},\; \int_{0}^{\infty} \frac{t^{delta-1+i\,gamma}}{\operatorname{exp}\left(1\,t\right)+1}\,dt \ne 0\right)\right)\right) \Leftrightarrow \operatorname{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/FermiMellin.salem_mellin_nonvanishing_iff_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Sanftenberg (2026). *Fermi Mellin proof slice from RiemannGaussian*. URL: <https://github.com/dbsanfte/RiemannGaussian/tree/e00f5c558703e7fda181988142e143bb27c1d2c7>.

*Commentary.*

Both implications use the actual complex integral. All real imaginary coordinates are quantified. The integral criterion implies the standard Riemann hypothesis by the frozen right-half-strip reduction.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_at_one`
- Truth anchor: `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_eq_of_ne_one`
- Truth anchor: `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_integrable`
- Truth anchor: `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_nonzero_iff_zeta_nonzero`
- Truth anchor: `D5/S3/Weil/ZetaBridge/FermiMellin.fermi_mellin_product_tendsto_one`
- Truth anchor: `D5/S3/Weil/ZetaBridge/FermiMellin.salem_mellin_nonvanishing_iff_rh`
- Dependency: [D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation](AlternatingZetaContinuation.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](RightHalfStripRiemannReduction.md)
