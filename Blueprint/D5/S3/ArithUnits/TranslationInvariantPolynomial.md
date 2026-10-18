# Translation-Invariant Polynomials

## Abstract

The additive orbit polynomial generates the algebra of translation invariants.

**Theorem 1.1 (A generator for nonzero translation invariants).**

Lean statement: `D5/S3/ArithUnits/TranslationInvariantPolynomial.exists_comp_of_translation_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/TranslationInvariantPolynomial.exists_comp_of_translation_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be any prime and K any field of characteristic p. For every nonzero a in K, every polynomial fixed by substitution T + a is a polynomial over the same field in T^p - a^(p-1) T. The field need not be finite or algebraically closed, and the polynomial may be zero or constant.

The generator is fixed by translation. Euclidean division by this monic polynomial preserves translation invariance of both the quotient and remainder, by uniqueness of division. The remainder has degree below p. Its values at the p distinct prime-field multiples of a agree, so interpolation makes it constant. Induction on degree then constructs the composition polynomial.

For a finite set S with S + a = S, its actual root polynomial, the product of T - x over x in S, is fixed by this substitution: translation by -a permutes the factors. It therefore has the same-field representation above. Empty S is included; its root polynomial is 1. This argument uses polynomial division and distinct roots rather than reversing Newton identities.

## References

- Truth anchor: `D5/S3/ArithUnits/TranslationInvariantPolynomial.exists_comp_of_translation_invariant`
