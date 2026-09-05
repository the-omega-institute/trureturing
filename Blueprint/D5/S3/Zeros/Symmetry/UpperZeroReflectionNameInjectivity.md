# Upper-Zero Reflection Name Injectivity

## Abstract

RH is equivalent to injectivity of the unordered reflection-orbit name on upper zeros.

**Theorem 1.1 (RH is injectivity of the upper reflection name).**

$$\forall Z: \operatorname{ZeroData},\ (\forall \rho\in \mathbb{C},\ \operatorname{IsNontrivialZero}(\rho) \Rightarrow \Re(\rho) = \operatorname{criticalAbscissa}) \Leftrightarrow \operatorname{Injective}(\operatorname{upperZeroReflectionName}(Z)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/UpperZeroReflectionNameInjectivity.rh_iff_upper_zero_reflection_name_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a supplied duplicate-free exhaustive ZeroData enumeration, the left side says that every classical nontrivial zero has critical real part. The right side says that the unordered conjugate-reflection orbit name is injective on indices whose zeros lie in the open upper half-plane.

Conjugate reflection is an involution preserving the upper half-plane. An index and its mirror always have the same unordered name, so injectivity forces every upper orbit to be a singleton. Conversely, singleton upper orbits reduce the name to an unordered repeated pair and hence make it injective.

The existing mirror fixed-point characterization converts singleton orbits into critical-line membership. Existing nonvanishing on the real interval and conjugation transport the upper-half-plane result to every nontrivial zero. The theorem constructs no ZeroData inhabitant and therefore does not assert RH unconditionally.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/UpperZeroReflectionNameInjectivity.rh_iff_upper_zero_reflection_name_injective`
- Dependency: [D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation](../../Weil/ZetaBridge/AlternatingZetaContinuation.md)
- Dependency: [D5/S3/Zeros/Symmetry/ZeroSymmetryAction](ZeroSymmetryAction.md)
