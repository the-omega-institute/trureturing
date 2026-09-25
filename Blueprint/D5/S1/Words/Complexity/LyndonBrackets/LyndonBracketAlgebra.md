# LyndonBracketAlgebra

## Abstract

Recursive standard brackets are homogeneous integral word polynomials.

The alphabet A is an arbitrary linearly ordered type throughout. Lyndon words, standard factorization, and the triangular standard-bracket construction are classical word and free-Lie-algebra material; the cited k-deck paper points to Chen-Fox-Lyndon, Lothaire, Radford, and Reutenauer. This module gives the Lean implementation used by the later actual-positive-word construction.

**Definition 1.1 (Integral word algebra).**

$$WordPolynomial$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.WordPolynomial` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

WordPolynomial A abbreviates MonoidAlgebra Z (FreeMonoid A), so monomials are finite words and coefficients are integers.

**Definition 1.2 (A word basis monomial).**

$$wordMonomial$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.wordMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

wordMonomial w is the monoid-algebra singleton at FreeMonoid.ofList w with coefficient one.

**Definition 1.3 (Homogeneous word polynomials).**

$$Homogeneous$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.Homogeneous` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Homogeneous p n means every monomial in the coefficient support of p has free-monoid length n.

**Definition 1.4 (Triangular leading word).**

$$HasLeadingWord$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.HasLeadingWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

HasLeadingWord p w requires p homogeneous of degree w.length, coefficient one at w, and every supported word lexicographically at least w.

**Definition 1.5 (The word-algebra commutator).**

$$commutator$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.commutator` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

commutator p q is p*q-q*p in the integral noncommutative word algebra.

**Definition 1.6 (Recursive standard bracketing).**

$$standardBracket$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.standardBracket` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

The empty word maps to zero, a singleton maps to its basis monomial, and a longer word maps to the commutator of the recursively bracketed standardLeft and standardRight factors.

**Theorem 1.7 (Standard brackets preserve length).**

$$standardBrackethomogeneous$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.standardBracket_homogeneous` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every word w, standardBracket w is homogeneous of degree w.length.

## References

- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.HasLeadingWord`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.Homogeneous`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.WordPolynomial`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.commutator`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.standardBracket`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.standardBracket_homogeneous`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra.wordMonomial`
- Dependency: [D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization](LyndonStandardFactorization.md)
