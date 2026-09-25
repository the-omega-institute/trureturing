# LyndonBracketLeading

## Abstract

Closed standard factors have their defining Lyndon word as leading monomial.

The alphabet A is an arbitrary linearly ordered type throughout. Lyndon words, standard factorization, and the triangular standard-bracket construction are classical word and free-Lie-algebra material; the cited k-deck paper points to Chen-Fox-Lyndon, Lothaire, Radford, and Reutenauer. This module gives the Lean implementation used by the later actual-positive-word construction.

**Definition 1.1 (Recursive word-theoretic closure).**

$$\operatorname{StandardFactorClosed}\left(empty\right) = False\land(\forall a,\operatorname{StandardFactorClosed}\left(\operatorname{singleton}\left(a\right)\right) = True)\land\forall w,2\leq\operatorname{length}\left(w\right)\Rightarrow\operatorname{StandardFactorClosed}\left(w\right)\iff\operatorname{StandardFactorClosed}\left(\operatorname{standardLeft}\left(w\right)\right)\land\operatorname{StandardFactorClosed}\left(\operatorname{standardRight}\left(w\right)\right)\land w<\operatorname{append}\left(\operatorname{standardRight}\left(w\right), \operatorname{standardLeft}\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading.StandardFactorClosed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

StandardFactorClosed is false on the empty word, true on singletons, and on longer words requires both standard factors recursively closed and the original word smaller than the reversed factor concatenation.

**Theorem 1.2 (Lyndon words satisfy the closure).**

$$\forall w,\operatorname{IsLyndon}\left(w\right)\Rightarrow\operatorname{StandardFactorClosed}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading.isLyndon_standardFactorClosed` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Every actual Lyndon word is StandardFactorClosed throughout its recursive longest-suffix factorization.

**Theorem 1.3 (The bracket is triangular).**

$$\forall w,\operatorname{StandardFactorClosed}\left(w\right)\Rightarrow\operatorname{HasLeadingWord}\left(\operatorname{standardBracket}\left(w\right), w\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading.standardBracket_hasLeadingWord` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every StandardFactorClosed word w, standardBracket w has leading word w with coefficient one and no lexicographically smaller supported word.

**Theorem 1.4 (Standard brackets are independent).**

$$\operatorname{LinearIndependent}\left(Z, \operatorname{standardBracket}\left(\operatorname{StandardFactorClosedWords}\left(A\right)\right)\right)$$

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
