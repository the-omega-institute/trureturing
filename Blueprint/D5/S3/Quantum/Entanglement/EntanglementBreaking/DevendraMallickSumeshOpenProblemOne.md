# Decomposability of 2-entanglement-breaking maps

## Abstract

A 2-entanglement-breaking map on complex matrices can be indecomposable.

**Definition 1.1 (The universal decomposability assertion).**

$$\forall a \in \mathrm{Npos},\; \forall b \in \mathrm{Npos},\; \forall f \in \operatorname{MatrixMap}\left(a, b\right),\; \operatorname{IsKEB}\left(2, f\right) \Rightarrow \operatorname{IsDecomposable}\left(f\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.claim` (`✓ std3`).

*Citation.* Repana Devendra, Nirupama Mallick and K. Sumesh (2023). *Mapping cone of k-entanglement breaking maps*. DOI: [10.1007/s11117-022-00956-4](https://doi.org/10.1007/s11117-022-00956-4). URL: <https://arxiv.org/abs/2105.14991v2>.

*Commentary.*

Open Problem 1, arXiv:2105.14991v2, p. 26: “Is every 2-EB map Φ : 𝕄₍d₁₎ → 𝕄₍d₂₎ decomposable?” The input and output dimensions are independently quantified in the positive naturals Npos. MatrixMap(a,b) is the type of complex-linear maps from the full a by a complex matrix algebra to the full b by b complex matrix algebra.

**Theorem 1.2 (An indecomposable 2-entanglement-breaking map).**

$$\exists d \in \mathrm{Npos},\; \exists f \in \operatorname{MatrixMap}\left(d, d\right),\; \operatorname{IsKEB}\left(2, f\right) \land \left(\neg \operatorname{IsDecomposable}\left(f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Repana Devendra, Nirupama Mallick and K. Sumesh (2023). *Mapping cone of k-entanglement breaking maps*. DOI: [10.1007/s11117-022-00956-4](https://doi.org/10.1007/s11117-022-00956-4). URL: <https://arxiv.org/abs/2105.14991v2>.

*Commentary.*

Taking k equal to two and both dimensions equal to 4194304 gives a 2-entanglement-breaking map that admits no decomposition into a completely positive and a completely copositive map.

**Theorem 1.3 (Refutation of universal decomposability).**

$$\neg \mathrm{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_refuted` (`✓ std3`). ∎

*Resolves.* `Problems/devendra-mallick-sumesh-2023-open-problem-1` (refuted) by `D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_refuted`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"devendra-mallick-sumesh-2023-open-problem-1","declaration_gid":"D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_refuted","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Repana Devendra, Nirupama Mallick and K. Sumesh (2023). *Mapping cone of k-entanglement breaking maps*. DOI: [10.1007/s11117-022-00956-4](https://doi.org/10.1007/s11117-022-00956-4). URL: <https://arxiv.org/abs/2105.14991v2>.

*Commentary.*

The square counterexample belongs to the class quantified by the universal assertion and violates its conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_counterexample`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_refuted`
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction](SignMatrixConstruction.md)
