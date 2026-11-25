# Articulation gluing of physical graph-state moments

## Abstract

A shared graph-state vertex has one exact rank increment and two normalized sampling channels.

**Theorem 1.1 (The reduced trace factors across a common vertex).**

$$G = xh1h2 + \frac{(g1 - xh1)(g2 - xh2)}{1 - x}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateArticulation.physical_articulation_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

Let two finite simple binary adjacency charts meet at exactly one vertex. For an arbitrary cut, h1 and h2 are the actual reduced trace moments after deleting the vertex in each chart, and g1 and g2 are the moments retaining it. The glued trace splits into the product of the deletion moments and the product of the surplus moments gi minus x hi, with x equal to two to the power one minus the real order K.

The common vertex adds a single row or column. Removing it leaves two diagonal blocks; restoring it raises the rank precisely when its border in at least one block lies outside that block's row or column span. The existing graph-state spectrum converts this Boolean OR into the displayed physical trace identity. This uses no approximation.

If the two normalized surplus channels and the two deletion channels admit classical laws, independent samples and XOR at the common vertex give the composed law. The readout table varies with the real order, while a constant readout of two violates the articulation identity. The theorem does not itself assert that each constituent channel has a law.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateArticulation.physical_articulation_readout`
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateConcentratableEntanglement](GraphStateConcentratableEntanglement.md)
