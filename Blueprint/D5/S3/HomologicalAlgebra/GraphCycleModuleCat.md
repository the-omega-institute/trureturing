# ModuleCat Homology of a Binary Graph Cycle Space

## Abstract

The binary one-dimensional `ModuleCat` homology of a finite simple graph is canonically its concrete simple-cycle space.

**Theorem 1.1 (Graph homology is the binary cycle space).** For a finite vertex type `V`, a finite simple graph `G`, and the chain object whose degree-one module is `G.edgeSet → ZMod 2` with endpoint-character differential, there is a `ModuleCat (ZMod 2)` isomorphism

$$
H_1(\operatorname{graphCycleComplex}(G))\;\cong\;
\operatorname{ModuleCat.of}(\mathbb F_2,\operatorname{simpleCycleSpace}(G)).
$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/GraphCycleModuleCat.graphCycleHomologyIso` (`✓ std3`). ∎

*Source.* Repository-derived finite binary specialization; the ordinary finite-graph homology/cycle-space correspondence is discussed by Diestel–Sprüssel, arXiv:0910.5634, Theorem 21.

## Commentary

The chain object has zero degree-two term, binary edge labels in degree one, and the endpoint-character linear combination as its differential. Mathlib's explicit `ShortComplex` homology identifies the homology object with the differential kernel after quotienting by the zero image. The existing finite-graph cycle-space theorem identifies that kernel with the span of indicators of simple closed cycles.

The statement is finite and uses ordinary graph homology over `ZMod 2`. It does not assert the path-homology quotient in characteristic different from two or an infinite-graph compactification result.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/GraphCycleModuleCat.graphCycleHomologyIso`
- Diestel–Sprüssel, “On the homology of locally finite graphs”, arXiv:0910.5634, Theorem 21.
