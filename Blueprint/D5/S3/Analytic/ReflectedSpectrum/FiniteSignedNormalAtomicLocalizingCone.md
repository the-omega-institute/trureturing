# Finite Signed-Normal Atomic Localizing Cone

## Abstract

Finite positive atomic moments separate mass positivity from signed support localization.

**Definition 1.1 (Ordinary finite atomic Hankel matrix).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finiteAtomicHankelMatrix`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finiteAtomicHankelMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary moment matrix is the Vandermonde evaluation congruence with the atomic masses on its diagonal. Its construction reuses the existing finite Vandermonde vocabulary and the repository Hermitian-form layer.

**Definition 1.2 (First support-localizing matrix).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finiteAtomicShiftedLocalizingMatrix`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finiteAtomicShiftedLocalizingMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shifted matrix uses mass times support as its diagonal atomic weight. It therefore tests the support half-line while leaving the ordinary positive-mass moment matrix unchanged.

**Definition 1.3 (Lagrange atom-isolation coefficients).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.lagrangeIsolationCoefficients`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.lagrangeIsolationCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At distinct support nodes, Cramer's rule applied to the existing Vandermonde matrix produces coefficients whose polynomial evaluations isolate one chosen atom exactly.

**Theorem 1.4 (Positive mass gives ordinary Hankel positivity).**

$$(\forall atom, 0 \leq \operatorname{mass}(atom)) \Rightarrow \operatorname{PosSemidef}(\operatorname{finiteAtomicHankelMatrix}(support, mass, depth))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finite_atomic_hankel_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative atomic diagonal is positive semidefinite, and congruence by the Vandermonde evaluation matrix preserves positive semidefiniteness. The support nodes may have either sign.

**Theorem 1.5 (A Lagrange isolator reads one shifted atom).**

$$\operatorname{Injective}(support) \Rightarrow \operatorname{hermForm}(\operatorname{finiteAtomicShiftedLocalizingMatrix}(support, mass, n), \operatorname{lagrangeIsolationCoefficients}(support, target)) = \operatorname{mass}(target) \times \operatorname{support}(target)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finite_atomic_shifted_localizing_lagrange_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the support map is injective, the Cramer coefficients evaluate to the chosen basis vector. The shifted Hermitian form then equals exactly the chosen mass times its support coordinate.

**Theorem 1.6 (Finite mass and support cones are separated).**

$$\operatorname{Injective}(support) \land (\forall atom, 0 \leq \operatorname{mass}(atom)) \land 0 < \operatorname{mass}(target) \land \operatorname{support}(target) < 0 \Rightarrow \operatorname{PosSemidef}(\operatorname{finiteAtomicHankelMatrix}(support, mass, n)) \land \operatorname{hermForm}(\operatorname{finiteAtomicShiftedLocalizingMatrix}(support, mass, n), \operatorname{lagrangeIsolationCoefficients}(support, target)) < 0 \land \neg \operatorname{PosSemidef}(\operatorname{finiteAtomicShiftedLocalizingMatrix}(support, mass, n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finite_signed_normal_atomic_localizing_cone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative masses force the ordinary Hankel matrix into the PSD cone. A positive-mass atom at a distinct negative support point is isolated by a finite polynomial, giving a strictly negative shifted readout.

Consequently the first support-localizing matrix is not positive semidefinite. This finite theorem distinguishes positive mass from support in the allowed half-line; it does not construct the completed-xi normal measure.

## References

- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finiteAtomicHankelMatrix`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finiteAtomicShiftedLocalizingMatrix`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finite_atomic_hankel_posSemidef`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finite_atomic_shifted_localizing_lagrange_readout`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.finite_signed_normal_atomic_localizing_cone`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.lagrangeIsolationCoefficients`
- Dependency: [D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare](../Adelic/ReflectedGrowthPairNegativeSquare.md)
- Dependency: [D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography](../GoldenTomography/FiniteVandermondeTomography.md)
