# Refuting the zero-fugacity degree formula

## Abstract

Refuting the zero-fugacity degree formula

Conjecture B.1 asserts a minimal-polynomial degree formula for every natural n at least two. The algebra is the full planar diagram algebra at loop fugacity zero. At n=9 the asserted value is 81, whereas an annihilating polynomial of degree 57 gives an upper bound of 57.

**Definition 1.1 (claim).**

$$\operatorname{claim} = \forall (n: \operatorname{Nat}), ((2 \le n) \to ((\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Polynomial}.\operatorname{natDegree}\left(\operatorname{minpoly}\left(\operatorname{Complex}, \operatorname{h}\left(\operatorname{Complex}, n\right)\right)\right)\right): \operatorname{Rat}) = \operatorname{HDiv}.\operatorname{hDiv}\left((((3: \operatorname{Rat}))^{(\operatorname{Nat}.\operatorname{div}\left((n) + (1), 2\right))}) + ((((-(1): \operatorname{Rat}))^{(n)}) \cdot (((3: \operatorname{Rat}))^{(\operatorname{Nat}.\operatorname{div}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right), 2\right))})), (2: \operatorname{Rat})\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.claim` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Appendix B.1, (B.13): natural division defines both exponents; Nat.sub is truncated. The outer division and the degree cast are in Rat.

**Theorem 1.2 (result).**

$$\operatorname{Not}\left(\operatorname{claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/poncini-rasmussen-2022-minpoly-degree-conjecture-b1` (refuted) by `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"poncini-rasmussen-2022-minpoly-degree-conjecture-b1","declaration_gid":"D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

The integer recurrence and literal diagram action give p(h_9)=0 for a monic polynomial of degree 57. The minimal polynomial therefore has degree at most 57, which contradicts the conjectured value 81. No exact degree is asserted.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra](../../Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction](PonciniRasmussenNineAction.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams](PonciniRasmussenNineDiagrams.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges](PonciniRasmussenNineEdges.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHorner](PonciniRasmussenNineHorner.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
