# Ranked contiguity for coface selections

## Abstract

Ranked contiguity for coface selections

**Theorem 1.1 (A coface selection gives a relative contiguity chain).**

Lean statement: `D5/S3/Topology/RankedCofaceContiguity.exists_relative_contiguity_of_chain_map`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/RankedCofaceContiguity.exists_relative_contiguity_of_chain_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Let the source preorder have a bounded strictly increasing natural rank. Suppose a map sends chains to chains and lies pointwise above an order map. Update the higher ranks first. Whenever a source chain contains both updated and unchanged vertices, an unchanged vertex below an updated one has its old image below the new image of the updated vertex. The images from each successive pair of stages form a single chain, and the two maps' agreement vertices stay fixed.

## References

- Truth anchor: `D5/S3/Topology/RankedCofaceContiguity.exists_relative_contiguity_of_chain_map`
- Dependency: [D5/S3/Topology/DescendingClosureContiguity](DescendingClosureContiguity.md)
