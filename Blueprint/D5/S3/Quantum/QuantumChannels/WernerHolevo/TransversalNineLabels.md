# Three blocks of order nine

## Abstract

Endpoint sums on three blocks of size nine.

**Theorem 1.1 (The endpoint sums biject onto the label group).**

$$\operatorname{Bijective}\left(\mathrm{edgeLabel}\right),\quad\mathrm{edgeLabel}:\quad\mathbb{Z}/3\times\operatorname{Edge}\left(\mathbb{F}_{9}\right)\to\mathbb{F}_{9}\times\mathbb{Z}/3\times(\mathbb{Z}/2)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineLabels.edgeLabel_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An edge consists of a block index modulo three and an unordered pair of distinct vertices in that block. Its endpoint sum has 108 possible values. The field coordinate fixes the midpoint. For each possible half-difference up to sign, the coordinate modulo three fixes the block. The two binary coordinates distinguish the four possible half-differences. This bijection supplies the edge labeling used in the gluing construction.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineLabels.edgeLabel_bijective`
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineAssembly](AffineNineAssembly.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineFinite](AffineNineFinite.md)
