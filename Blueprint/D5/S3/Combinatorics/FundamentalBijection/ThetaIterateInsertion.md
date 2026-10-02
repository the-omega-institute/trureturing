# Insertion of Three Letters

## Abstract

A three-letter insertion preserves two avoidance conditions and has a unique inverse on its specified boundary shape.

**Definition 1.1 (The three-letter insertion).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion.I`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion.I` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For a parameter of length h, I places h plus three and h plus two first, increases each parameter letter after the first by one, and finishes with one and h plus one.

**Theorem 1.2 (The successor word and avoidance after insertion).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion.insertion_scan`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion.insertion_scan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For a first-maximum parameter r of length h at least two, I(r) is a permutation of size h plus three. Its successor word is h plus two, the first h minus one entries of b(r) increased by one, one, the last entry of b(r) increased by one, and h plus three. Avoidance of 132 by r and by b(r) is respectively equivalent to avoidance by I(r) and by b(I(r)). Every permutation of size h plus three beginning with h plus three, h plus two and ending with one, h plus one has a unique first-maximum parameter preimage under I.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion.I`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion.insertion_scan`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateUFamilies](ThetaIterateUFamilies.md)
