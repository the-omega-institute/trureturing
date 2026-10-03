# Cycle Compatibility of Insertion

## Abstract

Insertion preserves the distinguished-cycle avoidance condition for inverse parameters.

**Theorem 1.1 (The inserted cycle and its image).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionCycle.insertion_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionCycle.insertion_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

If q is a permutation of size h at least two beginning with h and ending with one, let r be its inverse fundamental image. The image of I(r) is h plus three, followed by q increased by one, followed by h plus two and one, and the inverse image of this word is I(r). Moreover, P(I(r)) avoids 132 through depth two exactly when P(r) does.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionCycle.insertion_cycle`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks](ThetaBasicInverseBlocks.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion](ThetaIterateInsertion.md)
