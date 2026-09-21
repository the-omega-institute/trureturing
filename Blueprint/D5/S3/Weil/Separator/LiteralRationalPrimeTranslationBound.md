# Literal Rational Translation-Energy Modulus

## Abstract

Explicit rational coefficient budgets give a global translation-energy modulus for the exact literal smooth-transition Weil test.

**Theorem 1.1 (A global modulus from finite coefficient budgets).**

Lean statement: `D5/S3/Weil/Separator/LiteralRationalPrimeTranslationBound.literal_rational_prime_translation_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/LiteralRationalPrimeTranslationBound.literal_rational_prime_translation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural radius R and rational polynomials p and q, coefficientBudget sums the absolute coefficients weighted at B=2R. The resulting rational quantities A and D bound the values and derivatives of the real and imaginary even polynomial components throughout the support interval.

The proof derives an explicit derivative bound for expNegInvGlue and then proves that smoothTransition has derivative between zero and nine. This gives a global nine-Lipschitz estimate. Together with exact vanishing at both endpoints, support-crossing arguments extend the local polynomial estimates to a global amplitude bound A and Lipschitz constant K=D+(9/R)A for the exact literal function.

Translation energy is rewritten as mass minus twice a correlation. The difference of two correlations is localized to the union of their translated support intervals, whose measure is at most 8R. Integrating the pointwise A*K*|s-t| comparison yields |translationEnergy f s-translationEnergy f t| at most 32*R*A*K*|s-t| for all real shifts s and t.

The function f is required pointwise to equal the same literal smoothTransition(2-|y|/R)*rationalEvenPolynomial(p,q,y) used by the existing off-line-zero witness. This result transfers a certified shift width into an energy error bound. It does not enclose log n or square-root weights, aggregate the complete activePrimePowers set, certify a negative full-energy witness, assert an off-line zero, or prove the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Separator/LiteralRationalPrimeTranslationBound.literal_rational_prime_translation_bound`
- Dependency: [D5/S3/Weil/TestFunctions/RationalCutoffApproximation](../TestFunctions/RationalCutoffApproximation.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](../ZetaGamma/ArchimedeanJumpDecomposition.md)
