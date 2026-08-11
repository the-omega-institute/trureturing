# Zero Spectral Sharpness Characterises the Uniform Spectrum

## Abstract

Spectral sharpness vanishes exactly on the uniform spectrum.

**Theorem 1.1 (Spectral sharpness is zero iff the spectrum is uniform).**

$$\operatorname{sharp}(r) = \frac{1}{2}\sum_i \lvert r_i - r_{\operatorname{rev} i}\rvert\\\operatorname{sharp}(r) = 0 \iff \forall i, r_i = \frac{1}{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Sharpness/SpectralSharpness.spectral_sharpness_zero_iff_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectral sharpness of a spectrum r is the total variation between the spectrum and its reversal, sharp(r) = (1/2) sum_i |r_i - r_{rev i}|, equivalently half the L1 distance. For an antitone unit-sum spectrum on n points — a nonincreasing real vector summing to one, in particular any sorted probability spectrum, though nonnegativity is not needed — the sharpness vanishes exactly when the spectrum is uniform, that is r_i = 1/n for every i.

The summands of the sharpness are nonnegative, so a zero sharpness forces each |r_i - r_{rev i}| to vanish and the spectrum to equal its own reversal. In particular the first and last entries agree, and antitonicity squeezes every entry between these two equal values, so the spectrum is constant; the unit sum then pins that constant to 1/n. The converse is immediate, since a uniform spectrum equals its reversal and every summand vanishes.

This is the faithful-freedom-radius clause of the maximal-sharpness law: only the characterisation sharp(r) = 0 iff uniform is claimed here. The companion clauses of that law — the variational supremum realising the sharpness, the median-cut plus-or-minus-one witness, the qubit reduction to the Bloch radius, the full-rank saturation criterion for sharpness one, and the data-processing monotonicity of the sharpness — are not covered by this statement.

## References

- Truth anchor: `D5/S3/Quantum/Sharpness/SpectralSharpness.spectral_sharpness_zero_iff_uniform`
