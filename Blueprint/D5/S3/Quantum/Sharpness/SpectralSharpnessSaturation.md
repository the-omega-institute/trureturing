# Maximal Spectral Sharpness Characterises the Support-at-Most-Half Regime

## Abstract

Spectral sharpness attains its maximum exactly when the support is at most half the dimension.

**Theorem 1.1 (Spectral sharpness is one iff the support is at most half the dimension).**

$$\operatorname{sharp}(r) = 1 \iff \lvert \operatorname{supp}(r) \rvert \le \lfloor \frac{n}{2} \rfloor$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Sharpness/SpectralSharpnessSaturation.spectral_sharpness_one_iff_support_le_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectral sharpness of a spectrum r is the total variation between the spectrum and its reversal, sharp(r) = (1/2) sum_i |r_i - r_{rev i}|. For a probability spectrum on n points — antitone, nonnegative, and unit-sum — the sharpness attains its maximum value 1 exactly when the support (the set of nonzero entries) has cardinality at most floor(n/2). In words, freedom is maximally saturated without any pure state: it suffices that the support does not exceed half the dimension. Nonnegativity is a genuine load-bearing hypothesis here, used in the triangle-equality step.

Sharpness 1 is equivalent to mutual singularity of the spectrum and its reversal, that is r_i = 0 or r_{rev i} = 0 for every i: the total variation equals 1 iff every summand saturates the triangle bound |a - b| <= a + b, which for nonnegative entries forces one of r_i, r_{rev i} to vanish. Under antitonicity the support is a downward-closed prefix, so mutual singularity makes the support and its reversed image disjoint, giving 2 times the support size at most n, hence support size at most floor(n/2); conversely a prefix support of size at most floor(n/2) is disjoint from its reversal, which yields mutual singularity.

This records only the saturation clause sharp(r) = 1 iff support at most floor(n/2) of the maximal-sharpness law. The companion clauses of that law — the pure-state capacity, the spectral-pairing closed form of the tunable capacity, the variational supremum realising the sharpness, the median-cut plus-or-minus-one witness, and the minimal-endpoint characterisation sharp(r) = 0 iff the spectrum is uniform — are not covered by this statement.

## References

- Truth anchor: `D5/S3/Quantum/Sharpness/SpectralSharpnessSaturation.spectral_sharpness_one_iff_support_le_half`
- Dependency: [D5/S3/Quantum/Sharpness/SpectralSharpness](SpectralSharpness.md)
