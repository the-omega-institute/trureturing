# The spectral family of the original pair

## Abstract

Complex continuous spectral moments for the actual prescribed GNS coordinate.

The input algebra is any unital complex C-star algebra with its compatible star order. The positive functional psi and its completed GNS representation are genuine Mathlib objects. Its cyclic vector is unnormalized. Zero Hilbert spaces, singular functionals and spectral endpoints remain in scope.

**Definition 1.1 (The actual represented commutant).**

Lean statement: `D5/S3/Quantum/Analysis/GNSSpectralMoments.commutant`

*Formalization.* `D5/S3/Quantum/Analysis/GNSSpectralMoments.commutant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the star-subalgebra centralizer of the range of the actual GNS star homomorphism. The triple-centralizer identity makes this a concrete von Neumann algebra. No normality or faithfulness of the representation is needed.

**Theorem 1.2 (Exact membership).**

Lean statement: `D5/S3/Quantum/Analysis/GNSSpectralMoments.mem_commutant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSSpectralMoments.mem_commutant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bounded operator belongs to this von Neumann algebra exactly when it commutes with every represented algebra element. Closure of the range under star supplies both clauses of the star-subalgebra centralizer.

**Definition 1.3 (Full complex spectral calculus).**

Lean statement: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom`

*Formalization.* `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive contraction C, the complex spectrum is real and lies in [0,1]. Real part therefore defines a continuous map from the complex spectrum into the closed posterior interval. Precompose every complex continuous interval function by this map and apply Mathlib's complex cfcHom. The resulting map is a unital complex star algebra homomorphism into the bounded operators, including when the Hilbert space is zero.

**Theorem 1.4 (The indispensable first moment).**

Lean statement: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom_posterior`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The posterior function x maps exactly to the prescribed C. On its complex spectrum, the complex embedding of real part is the identity, by self-adjoint spectrum restriction. Thus the cfcHom identity theorem applies. The operator is not replaced by an unrelated coordinate.

**Theorem 1.5 (Agreement with real CFC).**

Lean statement: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom_real`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every globally continuous real function f, applying spectralHom to its complex-valued restriction to [0,1] gives the actual real cfc f C. Mathlib's real-to-complex CFC compatibility proves this equality. In particular it applies to every real overlap cutoff min(x,t(1-x)).

**Theorem 1.6 (Range in the full commutant).**

Lean statement: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom_commutes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom_commutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If C commutes with a bounded operator T, every spectral moment commutes with T, since C is self-adjoint. Applying this to each actual represented algebra element puts all moments in the genuine represented commutant.

**Definition 1.7 (Actual continuous coefficient outputs).**

Lean statement: `D5/S3/Quantum/Analysis/GNSSpectralMoments.momentMap`

*Formalization.* `D5/S3/Quantum/Analysis/GNSSpectralMoments.momentMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the spectral homomorphism with the existing continuous GNS coefficient functional a -> <Omega,Phi(g) pi(a) Omega>. This is a complex-linear map from all complex continuous interval functions to the actual continuous dual of the input algebra. Continuity in a comes from the existing operator-norm coefficient estimate.

**Definition 1.8 (The original pair's constructed family).**

Lean statement: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralFamily`

*Formalization.* `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Suppose C is a positive contraction in the represented commutant and its two actual coefficient functionals at C and I-C are rho and sigma. The constructed moment map is positive, since spectralHom preserves positivity and coefficient_nonneg_iff preserves operator positivity on the commutant. Unitality gives rho+sigma; the proved first moment gives rho. These prove membership in the existing full continuous-moment Family rho sigma. No Family, positive-map lift, representation normality, normalization, support condition or optimizer is assumed.

**Theorem 1.9 (Exact real overlap identification).**

Lean statement: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralFamily_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralFamily_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every continuous real f has spectral family moment equal to the actual GNS coefficient of cfc f C, as an equality of complex-linear functionals. The equality is consumed for every positive-threshold overlap in SpectralCentralizerEquality.

The CFC and coefficient ingredients are existing library results. The construction supplies the fixed-pair spectral family; general positive operator moment lifting and the necessary direction of the localized-centralizer classification are separate mathematical questions.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/GNSSpectralMoments.commutant`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSSpectralMoments.mem_commutant`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSSpectralMoments.momentMap`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralFamily`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralFamily_moment`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom_commutes`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom_posterior`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSSpectralMoments.spectralHom_real`
- Dependency: [D5/S3/Quantum/Analysis/GNSOrderCoordinates](GNSOrderCoordinates.md)
- Dependency: [D5/S3/Quantum/Analysis/NormalMomentFamily](NormalMomentFamily.md)
