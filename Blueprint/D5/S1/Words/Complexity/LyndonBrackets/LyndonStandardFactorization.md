# LyndonStandardFactorization

## Abstract

The longest Lyndon suffix gives the recursive standard factorization.

The alphabet A is an arbitrary linearly ordered type throughout. Lyndon words, standard factorization, and the triangular standard-bracket construction are classical word and free-Lie-algebra material; the cited k-deck paper points to Chen-Fox-Lyndon, Lothaire, Radford, and Reutenauer. This module gives the Lean implementation used by the later actual-positive-word construction.

**Definition 1.1 (The longest-Lyndon-suffix cut).**

$$\forall w,2\leq\operatorname{length}\left(w\right)\Rightarrow\operatorname{standardCut}\left(w\right) = \operatorname{min}\left(\operatorname{setOf}\left(i, 0, <,  , i, i, <, \operatorname{length}\left(w\right), \operatorname{IsLyndon}\left(\operatorname{drop}\left(w, i\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization.standardCut` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For w of length at least two, standardCut w is the least positive cut index whose suffix is Lyndon; hence it selects the longest proper Lyndon suffix.

**Definition 1.2 (Standard left factor).**

$$\forall w,2\leq\operatorname{length}\left(w\right)\Rightarrow\operatorname{standardLeft}\left(w\right) = \operatorname{take}\left(w, \operatorname{standardCut}\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization.standardLeft` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

standardLeft w hw is w.take (standardCut w hw) for a word whose length is at least two.

**Definition 1.3 (Standard right factor).**

$$\forall w,2\leq\operatorname{length}\left(w\right)\Rightarrow\operatorname{standardRight}\left(w\right) = \operatorname{drop}\left(w, \operatorname{standardCut}\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization.standardRight` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

standardRight w hw is w.drop (standardCut w hw), the longest proper Lyndon suffix.

**Theorem 1.4 (The left factor remains Lyndon).**

$$\forall w,2\leq\operatorname{length}\left(w\right)\land\operatorname{IsLyndon}\left(w\right)\Rightarrow\operatorname{IsLyndon}\left(\operatorname{standardLeft}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization.isLyndon_standardLeft` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

If w is Lyndon and has length at least two, then its standardLeft factor is Lyndon.

## References

- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization.isLyndon_standardLeft`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization.standardCut`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization.standardLeft`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization.standardRight`
- Dependency: [D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder](LyndonOrder.md)
