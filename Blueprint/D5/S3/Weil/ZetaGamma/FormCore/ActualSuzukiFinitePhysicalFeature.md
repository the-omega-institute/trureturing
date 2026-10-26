# Finite compressed profiles and actual compact physical features

## Abstract

Shared finite compressed-profile and compact physical-feature implementation, extracted without changing its mathematics.

**Definition 1.1 (The finite compressed profile).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressedProfile`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressedProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N and real kappa and t, this is the original finite profile evaluated at t/kappa. The finite cosine sum remains its private implementation.

**Definition 1.2 (The actual finite physical feature).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysicalFeature`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysicalFeature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is sourceOfProfile applied to the finite compressed profile: the original logarithmic physical construction, with no independent spectral input.

**Theorem 1.3 (Genuine finite Gamma density integrability).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_gamma_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_gamma_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural N and positive kappa, the actual Gamma-weighted squared Fourier norm of the compressed profile is integrable. The existing proof uses finite Fourier decay and the quadratic Gamma-weight bound.

**Theorem 1.4 (Every real constant-shift density is integrable).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_all_shift_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_all_shift_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural N, positive kappa and real c, the density with weight gammaWeight+c is integrable. Positivity of the shifted weight is not assumed.

**Theorem 1.5 (Exact compressed-profile support).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_zero_off`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_zero_off` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa the finite compressed profile vanishes outside the closed interval from kappa/4 to 3*kappa/4.

**Theorem 1.6 (The physical feature vanishes above four pi).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_zero_high`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_zero_high` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa at most one, the finite physical feature is zero at every x at least 4*pi. This support identity removes all higher physical theta terms.

**Theorem 1.7 (The complete physical theta sum).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_fullHasSum`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_fullHasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa at most one and every x at least pi, the complete physicalTerm series has HasSum equal to the same finite physical feature at x.

**Theorem 1.8 (The actual profile is the compressed finite profile).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_actualProfile_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_actualProfile_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa at most one, actualGammaProfile of the finite physical feature equals its finite compressed profile on the whole real line.

**Theorem 1.9 (The actual source belongs to every shifted Gamma domain).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_in_all_shift_domains`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_in_all_shift_domains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa at most one and every real c, the finite physical feature belongs to originalGammaFormDomain c. The proof uses the actual-profile identity and genuine shifted integrability.

**Theorem 1.10 (Lower density on each retained frequency band).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_band_density_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_band_density_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa at most one, each retained n in range(N+1), and kappa*xi in positiveBand n, the compressed positive-log Fourier density is at least kappa^2/(4096*pi).

**Theorem 1.11 (Uniform approximation by the finite physical feature).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_uniform_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_uniform_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa and every real x, the norm of compressedFeature kappa x minus the finite physical feature is at most (1/2)^(N+1).

**Theorem 1.12 (Continuity of the finite compressed profile).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N and real kappa, the finite compressed profile is continuous. This is the original composition proof.

**Theorem 1.13 (The finite physical feature is nonzero at its center).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_center_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_center_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa, the finite physical feature at pi*exp(kappa/2) is nonzero. This retained value prevents the later separated-feature cancellation from erasing the source.

**Theorem 1.14 (The actual finite feature is real valued).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_real`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N and real kappa and x, the imaginary part of the finite physical feature is zero.

**Theorem 1.15 (The compact physical support interval).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_support`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa, the support of the finite physical feature lies in the closed interval from pi to pi*exp(3*kappa/4).

**Theorem 1.16 (Continuity of the actual finite physical feature).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa, the literal finite physical feature is continuous. The existing proof uses a clamped expression only to establish continuity; the source definition is unchanged.

**Theorem 1.17 (The feature vanishes at and below pi).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_zero_le_pi`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_zero_le_pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa and x at most pi, the finite physical feature is zero, including its actual endpoint value.

**Theorem 1.18 (Compact support of every weighted square density).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_density_compact`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_density_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa and any real function w, the density w(x)*norm(finitePhysicalFeature N kappa x)^2 has compact support. No regularity of w is needed for this support statement.

**Theorem 1.19 (The finite feature satisfies original physical H6).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_h6`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_h6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa, continuity and compact support give originalPhysicalH6 of the same finite physical feature.

**Theorem 1.20 (Strictly positive physical mass).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_mass_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_mass_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa, the squared norm integral of the finite physical feature over x>pi is strictly positive.

**Theorem 1.21 (The physical sixth-moment cap).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_cap_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_cap_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa, the physical sixth moment is at most exp(9*kappa/2) times the physical mass of the same finite feature.

**Theorem 1.22 (A common physical mass upper bound).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_mass_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_mass_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive kappa at most one, the squared norm integral over x>pi is at most 3*pi.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressedProfile`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_all_shift_integrable`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_band_density_lower`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_continuous`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_gamma_integrable`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finiteCompressed_zero_off`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysicalFeature`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_actualProfile_eq`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_cap_bound`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_center_ne`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_continuous`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_density_compact`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_fullHasSum`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_h6`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_in_all_shift_domains`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_mass_pos`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_mass_upper`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_real`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_support`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_uniform_tail`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_zero_high`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFinitePhysicalFeature.finitePhysical_zero_le_pi`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample](ActualSuzukiDomainCounterexample.md)
