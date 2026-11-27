# Rank bounds for lifting simplicial flags

## Abstract

Rank bounds for lifting simplicial flags

**Theorem 1.1 (A flag is omitted when its witnesses exceed the available ranks).**

Lean statement: `D5/S3/Topology/RankedFiberLabelObstruction.flag_omitted_of_unique_support`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/RankedFiberLabelObstruction.flag_omitted_of_unique_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Each required coface contains a vertex whose old support includes a prescribed support. Assume there is only one eligible vertex in the enclosing face, projection preserves old support, and each coface label contains its projected vertex and stays in the source support. All required witnesses then project to the unique eligible vertex, and the ranks available in its fibre bound the distinct labels along a source chain.

**Theorem 1.2 (An isotone lift adds at least one source vertex per strict flag step).**

Lean statement: `D5/S3/Topology/RankedFiberLabelObstruction.card_add_le_of_lifted_flag_chain`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/RankedFiberLabelObstruction.card_add_le_of_lifted_flag_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

If the initial singleton target flag records the retracted source face, the source face starts with at least that cardinality. Along consecutive inclusion-comparable source faces, each strict increase in the assigned target flags forces a strict inclusion in the source.

## References

- Truth anchor: `D5/S3/Topology/RankedFiberLabelObstruction.card_add_le_of_lifted_flag_chain`
- Truth anchor: `D5/S3/Topology/RankedFiberLabelObstruction.flag_omitted_of_unique_support`
