# The Sec Grammar Support Region

## Abstract

The finite region of canonical states is exactly the support of every positive derivative iterate.

**Definition 1.1 (The finite support region).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarRegion.region`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarRegion.region` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

For a natural step n, region n is the finite set of family tags, indices, and multiplicities satisfying the canonical inequalities and parity conditions for step n.

**Theorem 1.2 (Reachability of the region).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarRegion.reachable_region`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/QGrammar/SecGrammarRegion.reachable_region` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

For every positive n, the support after n derivative steps is exactly the image under canonical encoding of region n.

## References

- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarRegion.reachable_region`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarRegion.region`
- Dependency: [D5/S3/Combinatorics/QGrammar/SecGrammarTransitions](SecGrammarTransitions.md)
