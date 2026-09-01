# Elliptic-Hyperbolic Reflection Trichotomy

## Abstract

Two-dimensional generators separate hyperbolic, neutral, and elliptic spectral sectors by determinant sign.

**Definition 1.1 (The reflected hyperbolic generator).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.hyperbolicGenerator`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.hyperbolicGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal rates delta and minus delta generate reciprocal growth and decay. Their trace cancels, their determinant is negative, and the generator square is positive scalar expansion.

**Definition 1.2 (The elliptic rotation generator).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.ellipticGenerator`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.ellipticGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The skew two-dimensional generator represents rotation at angular rate gamma. Its determinant is positive and its square is negative scalar curvature.

**Definition 1.3 (The neutral unsplit generator).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.neutralGenerator`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.neutralGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero generator is the boundary between the hyperbolic and elliptic sectors. Its trace, determinant, and square all vanish.

**Theorem 1.4 (The matrix determinant is the frozen reflected signed determinant).**

$$\forall delta: \mathbb{R}, \operatorname{det}(\operatorname{hyperbolicGenerator}(delta)) = \operatorname{reflectionPairSignedDeterminant}(delta).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.hyperbolic_det_eq_reflection_pair_signed_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix chart introduces no second negative-square invariant. Its determinant is identified exactly with the signed determinant already frozen for the reflected growth pair.

**Theorem 1.5 (Determinant sign separates the three finite sectors).**

$$\begin{aligned}\forall delta: \mathbb{R}, gamma: \mathbb{R}, \operatorname{trace}(\operatorname{hyperbolicGenerator}(delta)) = 0 \land \operatorname{det}(\operatorname{hyperbolicGenerator}(delta)) = -delta^{2} \land\\\operatorname{square}(\operatorname{hyperbolicGenerator}(delta)) = \operatorname{scalarIdentity}(delta^{2}) \land\\\operatorname{trace}(\operatorname{neutralGenerator}()) = 0 \land \operatorname{det}(\operatorname{neutralGenerator}()) = 0 \land \operatorname{square}(\operatorname{neutralGenerator}()) = 0 \land\\\operatorname{trace}(\operatorname{ellipticGenerator}(gamma)) = 0 \land \operatorname{det}(\operatorname{ellipticGenerator}(gamma)) = gamma^{2} \land\\\operatorname{square}(\operatorname{ellipticGenerator}(gamma)) = \operatorname{scalarIdentity}(-gamma^{2}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.elliptic_hyperbolic_reflection_trichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hyperbolic generator has determinant minus delta squared and square plus delta squared times the identity. The elliptic generator has determinant plus gamma squared and square minus gamma squared times the identity.

The neutral generator lies at determinant zero. This finite algebraic trichotomy supplies the local mode dictionary and does not assert that completed zeta has been realized by these matrices.

## References

- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.ellipticGenerator`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.elliptic_hyperbolic_reflection_trichotomy`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.hyperbolicGenerator`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.hyperbolic_det_eq_reflection_pair_signed_determinant`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.neutralGenerator`
- Dependency: [D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare](../Adelic/ReflectedGrowthPairNegativeSquare.md)
