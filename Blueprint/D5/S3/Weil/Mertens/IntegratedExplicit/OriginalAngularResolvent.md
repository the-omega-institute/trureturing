# The exact angular resolvent

## Abstract

The exact angular resolvent

The Fourier inversion and transform suppliers are imported from Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 under Apache 2.0. Fourier inversion is due to Sebastien Gouezel; the Fourier transform and improper exponential integrals are due to David Loeffler. Their upstream proofs are imported. The angular rescaling and the following proof chain are repository derivations.

**Theorem 1.1 (The normalized complex integral).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalAngularResolvent.angular_resolvent`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalAngularResolvent.angular_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real lag s, the literal complex integrand exp(I*w*s)/(1+4*w^2) is integrable, and (1/(2*pi))*integral exp(I*w*s)/(1+4*w^2)=exp(-abs(s)/2)/4. The proof integrates exp(-abs(t)/2) separately on its two half-lines, obtains its rational Fourier transform, applies Fourier inversion, then changes variables w=2*pi*xi. The statement includes s=0.

**Theorem 1.2 (The cosine formula).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalAngularResolvent.cosine_resolvent`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalAngularResolvent.cosine_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real part of the same integrable complex kernel gives the normalized cosine integral exp(-abs(s)/2)/4 for every real s. The finite-measure spectral construction uses angular_resolvent to obtain the complex resolvent identity, then takes real parts.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalAngularResolvent.angular_resolvent`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalAngularResolvent.cosine_resolvent`
