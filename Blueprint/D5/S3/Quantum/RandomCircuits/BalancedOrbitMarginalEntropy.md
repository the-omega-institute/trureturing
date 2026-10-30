# Equal average marginal entropies on a balanced unitary orbit

## Abstract

The two marginals of a balanced bipartite density state have equal Haar-averaged von Neumann entropies over its global unitary orbit.

**Definition 1.1 (The balanced marginal entropy identity).**

$$\operatorname{D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy.claim} = \forall \left(n: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\operatorname{MeasureTheory.integral}\left(\operatorname{MeasureTheory.Measure.haarMeasure}\left(\left(\operatorname{Top.top}: \operatorname{TopologicalSpace.PositiveCompacts}\left(\operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right)\right)\right)\right), \lambda \left(u: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right)\right) \mapsto \left(\operatorname{D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.marginalRight}\left(\operatorname{D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.unitaryConjugateState}\left(\left(\operatorname{Subtype.val}\left(u\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right), \operatorname{Subtype.property}\left(u\right), \rho\right)\right)\right)\right)\right) = \operatorname{MeasureTheory.integral}\left(\operatorname{MeasureTheory.Measure.haarMeasure}\left(\left(\operatorname{Top.top}: \operatorname{TopologicalSpace.PositiveCompacts}\left(\operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right)\right)\right)\right), \lambda \left(u: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right)\right) \mapsto \left(\operatorname{D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.marginalLeft}\left(\operatorname{D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.unitaryConjugateState}\left(\left(\operatorname{Subtype.val}\left(u\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right), \operatorname{Subtype.property}\left(u\right), \rho\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lin Zhang and Hua Xiang (2017). *Average entropy of a subsystem over a global unitary orbit of a mixed bipartite state*. DOI: [10.1007/s11128-017-1570-6](https://doi.org/10.1007/s11128-017-1570-6). URL: <https://arxiv.org/abs/1509.00211v3>.

*Commentary.*

For every natural n and every positive semidefinite trace-one state on the pair of n-dimensional factors, conjugate the state by a global unitary u. The right partial trace sums over the second coordinate, and the left partial trace sums over the first. The proposition equates the real Bochner integrals of the von Neumann entropies of these marginals against normalized Haar measure on the global unitary group. The top positive compact set is the entire compact group and fixes the Haar normalization. This is the balanced identity asked for in QINP-D-16-00527-revision.tex, lines 916–920, item (ii). The quantifiers range over all such states, including mixed states of arbitrary rank.

**Theorem 1.2 (Haar symmetry equates the two averages).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\operatorname{MeasureTheory.integral}\left(\operatorname{MeasureTheory.Measure.haarMeasure}\left(\left(\operatorname{Top.top}: \operatorname{TopologicalSpace.PositiveCompacts}\left(\operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right)\right)\right)\right), \lambda \left(u: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right)\right) \mapsto \left(\operatorname{D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.marginalRight}\left(\operatorname{D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.unitaryConjugateState}\left(\left(\operatorname{Subtype.val}\left(u\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right), \operatorname{Subtype.property}\left(u\right), \rho\right)\right)\right)\right)\right) = \operatorname{MeasureTheory.integral}\left(\operatorname{MeasureTheory.Measure.haarMeasure}\left(\left(\operatorname{Top.top}: \operatorname{TopologicalSpace.PositiveCompacts}\left(\operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right)\right)\right)\right), \lambda \left(u: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right)\right) \mapsto \left(\operatorname{D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.marginalLeft}\left(\operatorname{D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.unitaryConjugateState}\left(\left(\operatorname{Subtype.val}\left(u\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)\right), \operatorname{Subtype.property}\left(u\right), \rho\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-xiang-2017-balanced-orbit-marginal-entropy` (proved) by `D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-xiang-2017-balanced-orbit-marginal-entropy","declaration_gid":"D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lin Zhang and Hua Xiang (2017). *Average entropy of a subsystem over a global unitary orbit of a mixed bipartite state*. DOI: [10.1007/s11128-017-1570-6](https://doi.org/10.1007/s11128-017-1570-6). URL: <https://arxiv.org/abs/1509.00211v3>.

*Commentary.*

Let F be the permutation unitary associated with Equiv.prodComm on Fin n × Fin n. It exchanges the two coordinates. For any complex matrix x on this product, conjugation by F exchanges the partial traces: the right partial trace of F x F† is the left partial trace of x. Indeed, its entry at i,j is the sum over k of the entries of x at (k,i),(k,j), exactly the left partial trace.

Apply this matrix identity to u ρ u†. The adjoint of the product F u is u† F†, and associativity identifies (F u) ρ (F u)† with F (u ρ u†) F†. Passing through the matrix representation of density states and using equality of their underlying matrices gives equality of the right marginal at F u and the left marginal at u.

For each n and ρ, first use left invariance of Haar measure to replace u by F u in the integral of the right marginal entropy. The marginal equality then gives equality of the two entropy integrands at every u, hence almost everywhere. Equality of their integrals proves the displayed identity, answering item (ii) in QINP-D-16-00527-revision.tex, lines 916–920.

## References

- Truth anchor: `D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy.claim`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy.result`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner](../Entanglement/AbsolutePPT/UniformSchmidtCorner.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](HaarTwoCopyTwirl.md)
