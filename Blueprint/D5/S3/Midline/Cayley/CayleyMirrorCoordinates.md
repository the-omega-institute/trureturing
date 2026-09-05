# Cayley Mirror Coordinates

## Abstract

Conjugate reflection reverses the Cayley radius while preserving its phase.

**Theorem 1.1 (The mirror reverses radial drift and preserves phase).**

$$\begin{gathered}\forall s: \mathbb{C},\\{}\operatorname{c}\left(\operatorname{mirror}\left(s\right)\right) = \frac{1}{\overline{\operatorname{c}\left(s\right)}} \land\\{}\beta\left(\operatorname{mirror}\left(s\right)\right) = -\beta\left(s\right) \land\\{}\operatorname{AngleClass}\left(\operatorname{arg}\left(\operatorname{c}\left(\operatorname{mirror}\left(s\right)\right)\right)\right) = \operatorname{AngleClass}\left(\operatorname{arg}\left(\operatorname{c}\left(s\right)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/Cayley/CayleyMirrorCoordinates.cayley_mirror_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex point s, c(s) is the imported Cayley coefficient (s - 1)/s, mirror(s) is one minus the conjugate of s, and beta(s) is the imported logarithm of the coefficient norm.

The first public conjunct is the exact complex coefficient identity. Taking norms and logarithms gives the second conjunct, so the radial gain-loss direction is reversed.

The final conjunct casts both principal arguments to Real.Angle. Equality there is equality modulo two pi, including the negative real-axis branch endpoint, and states that the phase is preserved.

Pinned Mathlib supplies the argument laws for inversion and complex conjugation; the coefficient identity itself follows from the two imported coordinate definitions.

## References

- Truth anchor: `D5/S3/Midline/Cayley/CayleyMirrorCoordinates.cayley_mirror_coordinates`
- Dependency: [D5/S3/Midline/Cayley/LogarithmicRadialDefect](LogarithmicRadialDefect.md)
