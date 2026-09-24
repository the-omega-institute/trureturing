# Lyndon Standard Brackets and Leading Words

## Abstract

Lyndon words admit longest-suffix standard factorization, and their recursive integral brackets have triangular leading words and are linearly independent.

The alphabet A is an arbitrary linearly ordered type throughout. Lyndon words, standard factorization, and the triangular standard-bracket construction are classical word and free-Lie-algebra material; the cited k-deck paper points to Chen-Fox-Lyndon, Lothaire, Radford, and Reutenauer. This module gives the Lean implementation used by the later actual-positive-word construction.

**Definition 1.1 (Rotation-minimal Lyndon words).**

$$IsLyndon$$

*Formalization.* `D5/S1/Words/Complexity/LyndonStandardBracket.IsLyndon` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For w : List A, IsLyndon w means w is nonempty and, for every factorization w=u++v with u and v nonempty, w is strictly lexicographically smaller than v++u.

**Theorem 1.2 (Suffix characterization).**

$$isLyndoniffltsuffix$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonStandardBracket.isLyndon_iff_lt_suffix` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every word w, IsLyndon w is equivalent to w being nonempty and strictly smaller than every nonempty proper suffix v of w.

**Theorem 1.3 (Increasing concatenation is Lyndon).**

$$isLyndonappend$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonStandardBracket.isLyndon_append` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

If u and v are Lyndon and u<v in list lexicographic order, then u++v is Lyndon.

**Theorem 1.4 (A proper Lyndon suffix exists).**

$$existslyndonsuffixcut$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonStandardBracket.exists_lyndon_suffix_cut` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every w with 2<=w.length, there is i with 0<i<w.length such that w.drop i is Lyndon.

**Definition 1.5 (The longest-Lyndon-suffix cut).**

$$standardCut$$

*Formalization.* `D5/S1/Words/Complexity/LyndonStandardBracket.standardCut` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For w of length at least two, standardCut w is the least positive cut index whose suffix is Lyndon; hence it selects the longest proper Lyndon suffix.

**Definition 1.6 (Standard left factor).**

$$standardLeft$$

*Formalization.* `D5/S1/Words/Complexity/LyndonStandardBracket.standardLeft` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

standardLeft w hw is w.take (standardCut w hw) for a word whose length is at least two.

**Definition 1.7 (Standard right factor).**

$$standardRight$$

*Formalization.* `D5/S1/Words/Complexity/LyndonStandardBracket.standardRight` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

standardRight w hw is w.drop (standardCut w hw), the longest proper Lyndon suffix.

**Theorem 1.8 (The left factor remains Lyndon).**

$$isLyndonstandardLeft$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonStandardBracket.isLyndon_standardLeft` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

If w is Lyndon and has length at least two, then its standardLeft factor is Lyndon.

**Definition 1.9 (Integral word algebra).**

$$WordPolynomial$$

*Formalization.* `D5/S1/Words/Complexity/LyndonStandardBracket.WordPolynomial` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

WordPolynomial A abbreviates MonoidAlgebra Z (FreeMonoid A), so monomials are finite words and coefficients are integers.

**Definition 1.10 (A word basis monomial).**

$$wordMonomial$$

*Formalization.* `D5/S1/Words/Complexity/LyndonStandardBracket.wordMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

wordMonomial w is the monoid-algebra singleton at FreeMonoid.ofList w with coefficient one.

**Definition 1.11 (Homogeneous word polynomials).**

$$Homogeneous$$

*Formalization.* `D5/S1/Words/Complexity/LyndonStandardBracket.Homogeneous` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Homogeneous p n means every monomial in the coefficient support of p has free-monoid length n.

**Definition 1.12 (Triangular leading word).**

$$HasLeadingWord$$

*Formalization.* `D5/S1/Words/Complexity/LyndonStandardBracket.HasLeadingWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

HasLeadingWord p w requires p homogeneous of degree w.length, coefficient one at w, and every supported word lexicographically at least w.

**Definition 1.13 (The word-algebra commutator).**

$$commutator$$

*Formalization.* `D5/S1/Words/Complexity/LyndonStandardBracket.commutator` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

commutator p q is p*q-q*p in the integral noncommutative word algebra.

**Definition 1.14 (Recursive standard bracketing).**

$$standardBracket$$

*Formalization.* `D5/S1/Words/Complexity/LyndonStandardBracket.standardBracket` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

The empty word maps to zero, a singleton maps to its basis monomial, and a longer word maps to the commutator of the recursively bracketed standardLeft and standardRight factors.

**Theorem 1.15 (Standard brackets preserve length).**

$$standardBrackethomogeneous$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonStandardBracket.standardBracket_homogeneous` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every word w, standardBracket w is homogeneous of degree w.length.

**Definition 1.16 (Recursive word-theoretic closure).**

$$StandardFactorClosed$$

*Formalization.* `D5/S1/Words/Complexity/LyndonStandardBracket.StandardFactorClosed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

StandardFactorClosed is false on the empty word, true on singletons, and on longer words requires both standard factors recursively closed and the original word smaller than the reversed factor concatenation.

**Theorem 1.17 (Lyndon words satisfy the closure).**

$$isLyndonstandardFactorClosed$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonStandardBracket.isLyndon_standardFactorClosed` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Every actual Lyndon word is StandardFactorClosed throughout its recursive longest-suffix factorization.

**Theorem 1.18 (The bracket is triangular).**

$$standardBrackethasLeadingWord$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonStandardBracket.standardBracket_hasLeadingWord` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every StandardFactorClosed word w, standardBracket w has leading word w with coefficient one and no lexicographically smaller supported word.

**Theorem 1.19 (Standard brackets are independent).**

$$standardBracketlinearIndependent$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonStandardBracket.standardBracket_linearIndependent` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Over the integers, the family w |-> standardBracket w indexed by StandardFactorClosed words is linearly independent in all degrees jointly. The proof reads the least leading word in a finite relation.

## References

- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.HasLeadingWord`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.Homogeneous`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.IsLyndon`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.StandardFactorClosed`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.WordPolynomial`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.commutator`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.exists_lyndon_suffix_cut`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.isLyndon_append`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.isLyndon_iff_lt_suffix`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.isLyndon_standardFactorClosed`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.isLyndon_standardLeft`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.standardBracket`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.standardBracket_hasLeadingWord`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.standardBracket_homogeneous`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.standardBracket_linearIndependent`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.standardCut`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.standardLeft`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.standardRight`
- Truth anchor: `D5/S1/Words/Complexity/LyndonStandardBracket.wordMonomial`
