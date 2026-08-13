# Reflection Fixed-Point Contrast

## Abstract

Plain reflection fixes one point, while conjugate reflection fixes the critical line.

**Theorem 1.1 (Plain reflection fixes exactly one half).**

$$\forall s\in \mathbb{C},\ \operatorname{reflection}(s) = s \Leftrightarrow s = \frac{1}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/ReflectionFixedPointContrast.reflection_fixed_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex parameter, the frozen plain reflection s maps to one minus s fixes s exactly when s is one half. This is the point half of the source's point-versus-line contrast.

**Theorem 1.2 (Reflection and mirror fixed loci contrast).**

$$\{s\in \mathbb{C}:\operatorname{reflection}(s) = s\} = \{\frac{1}{2}\} \land \{s\in \mathbb{C}:\operatorname{mirror}(s) = s\} = \{s\in \mathbb{C}:\Re(s) = \frac{1}{2}\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/ReflectionFixedPointContrast.reflection_mirror_fixed_locus_contrast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first equality packages the point characterization as a singleton fixed set. The second equality is obtained directly from the frozen midline dual characterization, so conjugate reflection fixes every complex parameter with real part one half.

This declaration closes only the critical-line-existence subitem. It does not assert information-flow increments, information conservation, Wigner's dichotomy, an antiunitary-forcing mechanism, Lambda's numerical certificate, coexistence of the two information layers, or that zeta zeros lie on the fixed line.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/ReflectionFixedPointContrast.reflection_fixed_iff`
- Truth anchor: `D5/S3/Zeros/Symmetry/ReflectionFixedPointContrast.reflection_mirror_fixed_locus_contrast`
- Dependency: [D5/S3/Midline/DualCharacterization](../../Midline/DualCharacterization.md)
