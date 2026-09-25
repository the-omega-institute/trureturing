# LyndonBracketLeading

## Abstract

Closed standard factors have their defining Lyndon word as leading monomial.

The alphabet A is an arbitrary linearly ordered type throughout. Lyndon words, standard factorization, and the triangular standard-bracket construction are classical word and free-Lie-algebra material; the cited k-deck paper points to Chen-Fox-Lyndon, Lothaire, Radford, and Reutenauer. This module gives the Lean implementation used by the later actual-positive-word construction.

**Definition 1.1 (Recursive word-theoretic closure).**

$$StandardFactorClosed$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading.StandardFactorClosed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

StandardFactorClosed is false on the empty word, true on singletons, and on longer words requires both standard factors recursively closed and the original word smaller than the reversed factor concatenation.

**Theorem 1.2 (Lyndon words satisfy the closure).**

$$isLyndonstandardFactorClosed$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading.isLyndon_standardFactorClosed` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Every actual Lyndon word is StandardFactorClosed throughout its recursive longest-suffix factorization.

**Theorem 1.3 (The bracket is triangular).**

$$standardBrackethasLeadingWord$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading.standardBracket_hasLeadingWord` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every StandardFactorClosed word w, standardBracket w has leading word w with coefficient one and no lexicographically smaller supported word.

**Theorem 1.4 (Standard brackets are independent).**

$$standardBracketlinearIndependent$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading.standardBracket_linearIndependent` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Over the integers, the family w |-> standardBracket w indexed by StandardFactorClosed words is linearly independent in all degrees jointly. The proof reads the least leading word in a finite relation.

## References

- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading.StandardFactorClosed`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading.isLyndon_standardFactorClosed`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading.standardBracket_hasLeadingWord`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading.standardBracket_linearIndependent`
- Dependency: [D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra](LyndonBracketAlgebra.md)
