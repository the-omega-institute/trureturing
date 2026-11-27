# Disjoint close-pair defects and a strict Lorentz cap

## Abstract

Disjoint close-pair defects amplify into a strict Lorentz cap under a zero-phase bound.

**Theorem 1.1 (Finite matching defect inequality).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.finite_matching_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.finite_matching_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite collection of copies carries the inclusive closed radius-one neighborhoods. Two injective endpoint maps with disjoint images ensure that every selected row is counted once.

In the first endpoint neighborhood the two Lorentz weights are at least four fifths and one half. For the two chord lengths to a neighboring phase, the square of their sum is at most thirteen fourths of their weighted squared sum. The triangle inequality therefore gives four thirteenths of the endpoint phase residual per neighboring copy. All omitted terms are nonnegative.

**Theorem 1.2 (Defect for a spectrum with multiplicities).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.spectrum_matching_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.spectrum_matching_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite set of sigma-indexed copies counts each ordinate with its multiplicity through the inclusive cutoff. The copy-sum expansion identifies the ordered deficit with the difference of the Montgomery sums at zero and at the tested frequency.

**Theorem 1.3 (Conditional normalized cap).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.strict_normalized_cap_of_matching`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.strict_normalized_cap_of_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a cutoff above one, lower bounds proportional to the cutoff times its logarithm for the matching size and to its logarithm for the neighborhood copy counts, together with a nonnegative phase residual lower bound, give a normalized saving of at least four thirteenths of the product of their three constants.

If the normalized zero-phase sum is at most the target cap minus the chosen margin plus that saving, the normalized sum at the tested frequency is at most the target cap minus the margin. A positive margin gives a strict bound. Obtaining sufficiently many such close pairs with a uniform phase residual for actual zeta zeros across a long frequency band remains open.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.finite_matching_defect`
- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.spectrum_matching_defect`
- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.strict_normalized_cap_of_matching`
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit](MontgomeryAutocorrelationLimit.md)
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryCountUpper](MontgomeryCountUpper.md)
- Dependency: [D5/S3/Analytic/Oscillation/SmoothedSpectrumCounting](SmoothedSpectrumCounting.md)
