# A Four-Letter Refutation of the Abelian-Square Equality Claim

## Abstract

The binary word abab refutes the equality conclusion in Conjecture 4 on abelian squares.

**Definition 1.1 (Binary abelian squares).**

$$\forall u \in \operatorname{List}\left(Bool\right),\; (\operatorname{IsAbelianSquare}\left(u\right)) \Leftrightarrow (\operatorname{let} p := \operatorname{NatDiv}\left(\operatorname{length}\left(u\right), 2\right), (0 < p) \land \left((\operatorname{length}\left(u\right) = 2 \cdot p) \land \left((\operatorname{count}\left(false, \operatorname{take}\left(p, u\right)\right) = \operatorname{count}\left(false, \operatorname{drop}\left(p, u\right)\right)) \land (\operatorname{count}\left(true, \operatorname{take}\left(p, u\right)\right) = \operatorname{count}\left(true, \operatorname{drop}\left(p, u\right)\right))\right)\right))$$

*Formalization.* `D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.IsAbelianSquare` (`✓ std3`).

*Citation.* Szilárd Zsolt Fazekas, Adam Mammoliti, Robert Mercaş, Jamie Simpson (2026). *Binary Words Containing Few Abelian Squares*. DOI: [10.48550/arXiv.2604.23188](https://doi.org/10.48550/arXiv.2604.23188). URL: <https://arxiv.org/abs/2604.23188v1>.

*Commentary.*

The binary alphabet is encoded by a=false and b=true. NatDiv is floor division on natural numbers. The midpoint p is NatDiv(length(u),2), and both letter counts are equal across take(p,u) and drop(p,u).

**Definition 1.2 (Distinct abelian-square factors).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{abelianSquares}\left(w\right) = \operatorname{filter}\left(IsAbelianSquare, \operatorname{toFinset}\left(\operatorname{flatMap}\left(inits, \operatorname{tails}\left(w\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.abelianSquares` (`✓ std3`).

*Citation.* Szilárd Zsolt Fazekas, Adam Mammoliti, Robert Mercaş, Jamie Simpson (2026). *Binary Words Containing Few Abelian Squares*. DOI: [10.48550/arXiv.2604.23188](https://doi.org/10.48550/arXiv.2604.23188). URL: <https://arxiv.org/abs/2604.23188v1>.

*Commentary.*

The factors are prefixes of suffixes, formed by inits and tails. Converting them to a finite set removes repeated occurrences before filtering for abelian squares.

**Definition 1.3 (Trivial abelian squares).**

$$\forall u \in \operatorname{List}\left(Bool\right),\; (\operatorname{IsTrivial}\left(u\right)) \Leftrightarrow (\exists m \in \mathbb{N},\; (0 < m) \land ((u = \operatorname{replicate}\left(2 \cdot m, false\right)) \lor (u = \operatorname{replicate}\left(2 \cdot m, true\right))))$$

*Formalization.* `D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.IsTrivial` (`✓ std3`).

*Citation.* Szilárd Zsolt Fazekas, Adam Mammoliti, Robert Mercaş, Jamie Simpson (2026). *Binary Words Containing Few Abelian Squares*. DOI: [10.48550/arXiv.2604.23188](https://doi.org/10.48550/arXiv.2604.23188). URL: <https://arxiv.org/abs/2604.23188v1>.

*Commentary.*

A trivial abelian square is a positive even power of exactly one binary letter.

**Definition 1.4 (Conjecture 4).**

$$(claim) \Leftrightarrow (\forall w \in \operatorname{List}\left(Bool\right),\; (\operatorname{NatDiv}\left(\operatorname{length}\left(w\right), 4\right) \le \lvert \operatorname{abelianSquares}\left(w\right) \rvert) \land ((\lvert \operatorname{abelianSquares}\left(w\right) \rvert = \operatorname{NatDiv}\left(\operatorname{length}\left(w\right), 4\right)) \Rightarrow (\forall u \in \operatorname{abelianSquares}\left(w\right),\; \operatorname{IsTrivial}\left(u\right))))$$

*Formalization.* `D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.claim` (`✓ std3`).

*Citation.* Szilárd Zsolt Fazekas, Adam Mammoliti, Robert Mercaş, Jamie Simpson (2026). *Binary Words Containing Few Abelian Squares*. DOI: [10.48550/arXiv.2604.23188](https://doi.org/10.48550/arXiv.2604.23188). URL: <https://arxiv.org/abs/2604.23188v1>.

*Commentary.*

For every binary word w, NatDiv(length(w),4) is at most the number of distinct abelian-square factors. If equality holds, every such factor is asserted to be trivial.

**Theorem 1.5 (The equality conclusion fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For abab the distinct abelian-square factor set is the singleton containing abab, so its cardinality is NatDiv(4,4)=1. The factor abab contains both letters and is not a positive even power of either one. This refutes the conjunction through its equality conclusion and does not refute the lower bound.

## References

- Truth anchor: `D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.IsAbelianSquare`
- Truth anchor: `D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.IsTrivial`
- Truth anchor: `D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.abelianSquares`
- Truth anchor: `D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.claim`
- Truth anchor: `D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.result`
