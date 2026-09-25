# LyndonOrder

## Abstract

Lyndon words are ordered by their proper suffixes and admit Lyndon concatenation.

The alphabet A is an arbitrary linearly ordered type throughout. Lyndon words, standard factorization, and the triangular standard-bracket construction are classical word and free-Lie-algebra material; the cited k-deck paper points to Chen-Fox-Lyndon, Lothaire, Radford, and Reutenauer. This module gives the Lean implementation used by the later actual-positive-word construction.

**Definition 1.1 (Rotation-minimal Lyndon words).**

$$IsLyndon$$

*Formalization.* `D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder.IsLyndon` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For w : List A, IsLyndon w means w is nonempty and, for every factorization w=u++v with u and v nonempty, w is strictly lexicographically smaller than v++u.

**Theorem 1.2 (Suffix characterization).**

$$isLyndoniffltsuffix$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder.isLyndon_iff_lt_suffix` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every word w, IsLyndon w is equivalent to w being nonempty and strictly smaller than every nonempty proper suffix v of w.

**Theorem 1.3 (Increasing concatenation is Lyndon).**

$$isLyndonappend$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder.isLyndon_append` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

If u and v are Lyndon and u<v in list lexicographic order, then u++v is Lyndon.

**Theorem 1.4 (A proper Lyndon suffix exists).**

$$existslyndonsuffixcut$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder.exists_lyndon_suffix_cut` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every w with 2<=w.length, there is i with 0<i<w.length such that w.drop i is Lyndon.

## References

- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder.IsLyndon`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder.exists_lyndon_suffix_cut`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder.isLyndon_append`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder.isLyndon_iff_lt_suffix`
