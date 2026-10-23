# Full separability and exchanged diagonals

## Abstract

A fully separable finite state has zero coherence whenever an exchanged product-basis diagonal vanishes.

**Definition 1.1 (Joining complementary configurations).**

$$\forall V \in Type,\; \forall L \in Type,\; [\operatorname{DecidableEq}\left(V\right)], \forall J \in \operatorname{Finset}\left(V\right),\; \forall z \in (J)\to L,\; \forall x \in (\{v:V\mid \neg v \in J\})\to L,\; \forall v \in V,\; \operatorname{joinLocal}\left(J, z, x, v\right) = \operatorname{dite}\left(v \in J, (\lambda (h:v \in J) \mapsto z\left(\langle v,h\rangle\right)), (\lambda (h:\neg v \in J) \mapsto x\left(\langle v,h\rangle\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.joinLocal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite loss set J denotes its membership subtype in a carrier position. The complementary subtype contains the retained sites. The dependent conditional has a membership proof in its first branch and a nonmembership proof in its second branch.

**Definition 1.2 (Partial trace over any finite loss set).**

$$\forall V \in Type,\; \forall L \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)], \forall rho \in \operatorname{Matrix}\left((V)\to L, (V)\to L, \mathbb{C}\right),\; \forall J \in \operatorname{Finset}\left(V\right),\; \operatorname{partialTraceLocal}\left(rho, J\right) = \operatorname{partialTraceFirst}\left(\operatorname{Matrix.submatrix}\left(rho, (\lambda (q:((J)\to L) \times ((\{v:V\mid \neg v \in J\})\to L)) \mapsto \operatorname{joinLocal}\left(J, \operatorname{Prod.fst}\left(q\right), \operatorname{Prod.snd}\left(q\right)\right)), (\lambda (q:((J)\to L) \times ((\{v:V\mid \neg v \in J\})\to L)) \mapsto \operatorname{joinLocal}\left(J, \operatorname{Prod.fst}\left(q\right), \operatorname{Prod.snd}\left(q\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.partialTraceLocal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input matrix is reindexed by the join of the lost and retained configurations. The existing partialTraceFirst sums the same lost configuration in both indices, giving the usual finite partial trace.

**Definition 1.3 (Finite convex mixtures of local density states).**

$$\forall V \in Type,\; \forall L \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)], \forall rho \in \operatorname{Matrix}\left((V)\to L, (V)\to L, \mathbb{C}\right),\; \operatorname{IsFullySeparableLocal}\left(rho\right) \Leftrightarrow (\exists k \in \mathbb{N},\; \exists p \in (\operatorname{Fin}\left(k\right))\to \mathbb{R},\; \exists sigma \in (\operatorname{Fin}\left(k\right))\to (V)\to \operatorname{DensityState}\left(L\right),\; (\forall j \in \operatorname{Fin}\left(k\right),\; 0 \le p\left(j\right)) \land ((\sum_{j:\operatorname{Fin}\left(k\right)} (p\left(j\right)) = 1) \land (\forall x \in (V)\to L,\; \forall y \in (V)\to L,\; rho\left(x, y\right) = \sum_{j:\operatorname{Fin}\left(k\right)} (\operatorname{Complex.ofReal}\left(p\left(j\right)\right) \cdot \prod_{v:V} (\operatorname{val}\left(sigma\left(j, v\right)\right)\left(x\left(v\right), y\left(v\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.IsFullySeparableLocal` (`✓ std3`).

*Citation.* G. M. Quinta; R. André; A. Burchardt; K. Życzkowski (2019). *Cut-resistant links and multipartite entanglement resistant to particle loss*. DOI: [10.1103/PhysRevA.100.062329](https://doi.org/10.1103/PhysRevA.100.062329). URL: <https://arxiv.org/abs/1908.10390v1>.

*Commentary.*

Full separability is a convex combination of product states. Each DensityState L is a positive trace-one local matrix, val forgets its proof, and Complex.ofReal embeds each nonnegative real mixture weight into the complex scalars. The product and sum are over all sites and all mixture indices.

**Theorem 1.4 (Density states are positive semidefinite).**

$$\forall L \in Type,\; [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)], \forall sigma \in \operatorname{DensityState}\left(L\right),\; \operatorname{Matrix.PosSemidef}\left(\operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(sigma\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.density_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite local carrier L, forgetting the CStarMatrix wrapper of a DensityState L gives a positive semidefinite complex matrix. Positivity is transported through CStarMatrix.ofMatrixStarAlgEquiv.symm.

**Theorem 1.5 (A zero exchanged diagonal annihilates coherence).**

$$\forall V \in Type,\; \forall L \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)], \forall rho \in \operatorname{Matrix}\left((V)\to L, (V)\to L, \mathbb{C}\right),\; \forall x \in (V)\to L,\; \forall y \in (V)\to L,\; \forall i \in V,\; (\operatorname{IsFullySeparableLocal}\left(rho\right)) \Rightarrow ((rho\left(\operatorname{Function.update}\left(x, i, y\left(i\right)\right), \operatorname{Function.update}\left(x, i, y\left(i\right)\right)\right) = 0) \Rightarrow (rho\left(x, y\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.separable_exchange_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write rho as a convex sum of products of local density matrices. All terms on the exchanged diagonal are nonnegative. If their sum is zero, each weighted product has a zero factor. Positivity makes the corresponding local row or column zero, so every summand of rho(x,y) vanishes. The contrapositive detects entanglement from a nonzero coherence and a zero exchanged diagonal.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.IsFullySeparableLocal`
- Truth anchor: `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.density_psd`
- Truth anchor: `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.joinLocal`
- Truth anchor: `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.partialTraceLocal`
- Truth anchor: `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.separable_exchange_zero`
- Dependency: [D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence](LocalObservationPartialTraceEquivalence.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
