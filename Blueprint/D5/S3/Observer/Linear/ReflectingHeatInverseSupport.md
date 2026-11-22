# Inverse Fourier support of the reflecting heat interpolant

## Abstract

The reflecting heat interpolant has a centered inverse density with the prescribed exponential moments.

**Theorem 1.1 (Centered density and reflecting mode moments).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatInverseSupport.momentInterpolant_inverse_support`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatInverseSupport.momentInterpolant_inverse_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an entire multiplier with the prescribed radial half-width L/2 and the real-axis Joukowski bound, the reflecting heat interpolant satisfies the directional bound of order n minus two plus m and has a square-integrable real restriction. The inverse Fourier support theorem gives an integrable representative of its inverse L2 class, vanishing at every point outside the centered interval of length L.

The transform of this density with angular kernel exp(-i z t) is entire by differentiation under the integral. Classical Fourier agreement on the real axis and the identity theorem recover the interpolant on the whole plane. At the node minus i times the reflecting rate, the kernel becomes the corresponding real decaying exponential. The moment is zero off the target mode and equals the nodal derivative times the multiplier at the target node on that mode.

## References

- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatInverseSupport.momentInterpolant_inverse_support`
- Dependency: [D5/S3/Fourier/InverseFourierSupport](../../Fourier/InverseFourierSupport.md)
- Dependency: [D5/S3/Observer/Linear/ReflectingHeatDirectionalBound](ReflectingHeatDirectionalBound.md)
