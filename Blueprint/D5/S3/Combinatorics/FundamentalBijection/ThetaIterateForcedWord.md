# Classification at the First Endpoint

## Abstract

First-maximum parameters fall into explicit families or a recursively inserted cycle family.

**Definition 1.1 (The balanced two-block word).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateForcedWord.W`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateForcedWord.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For size h and a equal to the integer part of (h plus one) divided by two, W(h) consists of h down to a plus one, then a minus one down to one, then a.

**Theorem 1.2 (Explicit words and recursive insertion).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateForcedWord.first_endpoint_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateForcedWord.first_endpoint_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Let r be a permutation of size h at least four beginning with h, and suppose r, b(r), and its fundamental image avoid 132. Then r is U(h), is decreasing, or begins with h, h minus one, has penultimate value one and terminal value v between two and h minus two, and has its cycle from h equal to its fundamental image. In the third case v below h minus two forces r = W(h); when v = h minus two and h is at least five, r has a unique representation as I of a first-maximum parameter of size h minus three whose P image avoids through depth two and whose cycle from its maximum equals its fundamental image.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateForcedWord.W`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateForcedWord.first_endpoint_classification`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleScan](ThetaIterateCycleScan.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion](ThetaIterateInsertion.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionInverse](ThetaIterateInsertionInverse.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateShortCycle](ThetaIterateShortCycle.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateUFamilies](ThetaIterateUFamilies.md)
