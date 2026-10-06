# ModuleCat Homology of a Binary Graph Cycle Space

## Abstract

The binary one-dimensional ModuleCat homology of a finite simple graph is canonically its concrete simple-cycle space.

**Theorem 1.1 (Graph homology is the binary cycle space).**

$$\forall V: \operatorname{Type}, [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G: \operatorname{simpleGraph}\left(V\right), [\operatorname{Fintype}\left(\operatorname{edgeSet}\left(G\right)\right)], [\operatorname{Fintype}\left(\operatorname{connectedComponent}\left(G\right)\right)] \operatorname{homology}\left(\operatorname{graphCycleComplex}\left(G\right)\right) \equiv \operatorname{ModuleCatOf}\left(\operatorname{ZMod}\left(2\right), \operatorname{simpleCycleSpace}\left(G\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/GraphCycleModuleCat.graphCycleHomologyIso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite vertex type V and a finite simple graph G, the chain object in degree one is the module of binary edge labels. Its differential is the finite linear combination of the two endpoint characters, and the degree-two object is zero. The resulting ShortComplex therefore has a genuine ModuleCat homology object.

The proof uses Mathlib's explicit ModuleCat homology quotient. The image of the zero degree-two map is bottom, so the quotient is linearly equivalent to the differential kernel. The existing finite-graph cycle-space theorem identifies that kernel with the span of indicators of simple closed cycles, yielding the displayed categorical isomorphism.

This is the finite binary specialization of the ordinary finite-graph homology/cycle-space correspondence discussed by Diestel and Sprüssel (arXiv:0910.5634, Theorem 21). It does not assert the path-homology quotient used for characteristic different from two, and it does not cover infinite Freudenthal compactifications.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/GraphCycleModuleCat.graphCycleHomologyIso`
- Dependency: [D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace](../Fourier/CharacterSelection/SimpleGraphCycleSpace.md)
