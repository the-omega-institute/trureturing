# Weighted Dyck Paths in a Strip

## Abstract

Narayana weights and their signed counterparts give two polynomial sums over Dyck paths confined to an even strip.

**Definition 1.1 (Prefix height).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.heightAfter`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.heightAfter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

A path is a finite sequence of Boolean steps, with true denoting an up-step and false a down-step. Its height after k steps is the sum of the first k increments, each up-step contributing one and each down-step contributing minus one. If k exceeds the path length, the entire path is used.

**Definition 1.2 (Dyck paths of bounded height).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.IsStripDyck`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.IsStripDyck` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For a natural number h, a path is a Dyck path in the strip of height h when every prefix, including the empty prefix, has height between zero and h, inclusive, and its final height is zero.

**Definition 1.3 (The weight of a path).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.weight`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.weight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Given a sequence tau of integer polynomials, the weight of a path is the product of its step weights. An up-step has weight one. A down-step arriving at height k has weight tau(k), with a negative arrival height replaced by zero. The empty path has weight one.

**Definition 1.4 (The weighted strip sum).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.stripSum`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.stripSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For natural numbers h and n and a polynomial weight sequence tau, stripSum is the sum of the weights of all Dyck paths of length 2n in the strip of height h. Each Boolean sequence of length 2n contributes its weight if it satisfies the strip condition and zero otherwise.

**Definition 1.5 (The number of strip paths).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.stripCount`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.stripCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For natural numbers h and j, stripCount is the number of Dyck paths of length 2j in the strip of height h. Equivalently, it is the cardinality of the Boolean sequences of length 2j whose prefix heights lie between zero and h and whose final height is zero.

**Definition 1.6 (Narayana weights).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.tauPlus`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.tauPlus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

The Narayana weight sequence is one at every even arrival height and t at every odd arrival height, where t is the indeterminate of the integer polynomial ring. Thus its successive entries are 1, t, 1, t, and so on.

**Definition 1.7 (Signed Narayana weights).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.tauMinus`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.tauMinus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

The signed weight sequence has period four, with entries 1, t, minus one and minus t at arrival heights congruent to zero, one, two and three modulo four, respectively.

**Definition 1.8 (The two even-strip expansions).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.claim`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every positive integer m and nonnegative integer n, let A_j be the number of Dyck paths of semilength j in the strip of height m minus one. The Narayana-weighted sum of paths of semilength n plus one in the strip of height 2m equals the sum, over j from zero through floor(n/2), of A_j times binom(n, 2j) times t^j times (1 + t)^(n - 2j). The signed weighted sum equals the sum over the same range of (-1)^j times A_j times binom(floor(n/2), j) times t^j times (1 + t)^(n - 2j). Both equalities are identities of integer polynomials.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.IsStripDyck`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.heightAfter`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.stripCount`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.stripSum`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.tauMinus`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.tauPlus`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.weight`
