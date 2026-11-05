# Finite entire separation controls all translates

## Abstract

Finite entire separation controls all translates.

**Theorem 1.1 (Finite entire separation controls all translates).**

Lean statement: `D5/S3/Analytic/Entire/SeparatedKernel.finite_translation_space_of_separated_hankel`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/SeparatedKernel.finite_translation_space_of_separated_hankel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SeparatedLE(k,F) requires two families indexed by Fin k of entire complex functions whose pointwise product sum equals F at every complex pair. FiniteSeparated means such a natural k exists. Arbitrary entire factors are allowed; they are not assigned Hilbert vectors or polynomial coefficients.

The complete translation span of f is contained in the finite span of the first separated family whenever f(z+w) is finitely separated. This applies to every complex translate, rather than a finite set of samples. Finite dimension follows by inclusion into that actual finite factor span.

Addition, multiplication, scalar multiplication, polynomial evaluation, differentiation in either variable and linear changes of either variable preserve finite separation with the stated exact term bounds. These helpers are consumed by the weighted-kernel and physical-channel proofs. No matrix cutoff or growth hypothesis is imposed.

## References

- Truth anchor: `D5/S3/Analytic/Entire/SeparatedKernel.finite_translation_space_of_separated_hankel`
- Dependency: [D5/S3/Analytic/Entire/TranslationFinite](TranslationFinite.md)
