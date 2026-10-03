# Coefficients of the Narayana Strip Product

## Abstract

The product formula for bounded Narayana series is expressed as equality of polynomial coefficients at heights 4m and 4m + 1.

**Definition 1.1 (The squared-parameter coefficient).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs.lhsCoeff`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs.lhsCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For nonnegative integers h and N, the coefficient of z^N in C^{(h)}(t^2, z^2) is zero when N is odd. When N is even, it is the Narayana-weighted sum over Dyck paths of semilength N/2 confined to heights zero through h, with t replaced by t^2. Each up-step has weight one, and each down-step arriving at height k has weight one for even k and t for odd k before this substitution.

**Definition 1.2 (The signed convolution coefficient).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs.rhsCoeff`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs.rhsCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For nonnegative integers h and N, the coefficient of z^N in c^{(h)}(t, z)c^{(h)}(-t, -z) is the sum over i from zero through N of c_i^{(h)}(t) times (-1)^(N - i) times c_{N-i}^{(h)}(-t). Here c_j^{(h)}(t) is the weighted sum over Dyck paths of semilength j confined to heights zero through h, with up-step weight one and down-step arrival weights repeating 1, t, -1, -t.

**Definition 1.3 (The two strip product identities).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs.claim`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every positive integer m and every nonnegative integer N, the coefficient of z^N in C^{(4m)}(t^2, z^2) equals the coefficient of z^N in c^{(4m)}(t, z)c^{(4m)}(-t, -z), and the same coefficient equality holds at height 4m + 1. Both equalities are identities of polynomials in t with integer coefficients. This is the coefficientwise form of Conjecture 2, equation (79), of Cigler's paper.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs.lhsCoeff`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs.rhsCoeff`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs](CiglerStripExpansionDefs.md)
