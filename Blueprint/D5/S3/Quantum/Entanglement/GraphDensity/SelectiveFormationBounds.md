# SelectiveFormationBounds

## Abstract

Coordinate-block formation lower bound and exact embedding.

Scalar quotients are real unless a complex cast is displayed. Fin indices are zero based. Matrix, rankOneDensity, partialTraceRight and partialTransposeB denote the actual Lean operations. All entropy values are in bits.

**Definition 1.1 (pairEquiv).**

$$\forall (k:\mathbb N), \operatorname{pairEquiv}\left(k\right)=\operatorname{finProdFinEquiv}.\operatorname{trans}(\operatorname{finCongr}\left(\operatorname{Nat}.\operatorname{mul}_{comm}(k,2)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds.pairEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

The literal Lean expression is finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2)); the equality proof only casts k·2 to 2·k.

**Theorem 1.2 (pairEquiv_val).**

$$\forall (k:\mathbb N), \forall (j:\operatorname{Fin}\left(k\right)), \forall (b:\operatorname{Fin}\left(2\right)), \operatorname{val}\left(\operatorname{pairEquiv}\left(k\right)((j,b))\right)=\operatorname{val}\left(b\right)+2\cdot \operatorname{val}\left(j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds.pairEquiv_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Definition 1.3 (embedState).**

$$\forall (k:\mathbb N), \forall (j:\operatorname{Fin}\left(k\right)), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right)), \mathbb C\right)), \forall (x:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\cdot k\right))), \forall (y:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\cdot k\right))), \operatorname{embedState}\left(j, \rho\right)(x,y)=\operatorname{ite}\left((\operatorname{pairEquiv}\left(k\right).\operatorname{symm}(x.2).1=j)\land (\operatorname{pairEquiv}\left(k\right).\operatorname{symm}(y.2).1=j), \rho((x.1,\operatorname{pairEquiv}\left(k\right).\operatorname{symm}(x.2).2),(y.1,\operatorname{pairEquiv}\left(k\right).\operatorname{symm}(y.2).2)), 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds.embedState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean definition; every displayed parameter is quantified.

**Theorem 1.4 (embedded_formation_lower).**

$$\forall (k:\mathbb N), \forall (j:\operatorname{Fin}\left(k\right)), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right)), \mathbb C\right)), (\operatorname{Nonempty}\left(\operatorname{Ensemble}\left(\operatorname{embedState}\left(j, \rho\right)\right)\right))\longrightarrow E_F(\rho)\le E_F(\operatorname{embedState}\left(j, \rho\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds.embedded_formation_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Compressing an ensemble supported in a single coordinate block preserves its pure marginal entropy; taking the infimum gives the lower bound.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds.embedState`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds.embedded_formation_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds.pairEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds.pairEquiv_val`
- Dependency: [D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds](FormationBounds.md)
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](../../Information/SeparableStateLocalUnitaryStabilizerObstruction.md)
