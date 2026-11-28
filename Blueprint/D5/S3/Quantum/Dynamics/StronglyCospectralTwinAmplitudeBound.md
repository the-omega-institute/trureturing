# Return amplitudes of strongly cospectral twins

## Abstract

Every odd integer relation among the supported adjacency gaps of strongly cospectral twins gives an explicit positive floor for their return amplitudes.

**Definition 1.1 (The twin eigenvalue).**

$$\forall (n: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall (u: \operatorname{Fin}\left(n\right)), (\forall (v: \operatorname{Fin}\left(n\right)), (((\operatorname{Adj}\left(G, u, v\right)) \to (\theta\left(G, u, v\right) = -1)) \land ((\neg \operatorname{Adj}\left(G, u, v\right)) \to (\theta\left(G, u, v\right) = 0))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound.twinEigenvalue` (`✓ std3`).

*Citation.* Karen Meagher, Hermie Monterde, Tung T. Nguyen (2026). *Sedentariness in Cayley graphs*. DOI: [10.48550/arXiv.2611.00567](https://doi.org/10.48550/arXiv.2611.00567). URL: <https://arxiv.org/abs/2611.00567v1>.

*Commentary.*

The difference of the two vertex basis vectors has eigenvalue minus one for adjacent twins and zero for nonadjacent twins.

**Definition 1.2 (The remaining adjacency support).**

$$\forall (n: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall (u: \operatorname{Fin}\left(n\right)), (\forall (v: \operatorname{Fin}\left(n\right)), (\forall (e: \mathbb{R}), ((e \in \operatorname{J}\left(G, u, v\right)) \Leftrightarrow ((e \in \operatorname{spectrum}\left(G\right)) \land ((e \ne \theta\left(G, u, v\right)) \land (0 < \operatorname{a}\left(G, u, e\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound.remainingSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Karen Meagher, Hermie Monterde, Tung T. Nguyen (2026). *Sedentariness in Cayley graphs*. DOI: [10.48550/arXiv.2611.00567](https://doi.org/10.48550/arXiv.2611.00567). URL: <https://arxiv.org/abs/2611.00567v1>.

*Commentary.*

The finite support contains the distinct eigenvalues whose projector diagonals at the first twin are positive, excluding the twin eigenvalue. Each projector combines all basis vectors of its eigenspace.

**Theorem 1.3 (The odd-relation return-amplitude bound).**

$$\forall (n: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall (u: \operatorname{Fin}\left(n\right)), (\forall (v: \operatorname{Fin}\left(n\right)), (((u \ne v) \land ((\forall (x: \operatorname{Fin}\left(n\right)), (((x \ne u) \land (x \ne v)) \to ((\operatorname{Adj}\left(G, x, u\right)) \Leftrightarrow (\operatorname{Adj}\left(G, x, v\right))))) \land (\operatorname{StronglyCospectral}\left(G, u, v\right)))) \to ((\operatorname{E}\left(G, \theta\left(G, u, v\right)\right) \cdot \operatorname{single}\left(u\right) = \frac{1}{2} \cdot (\operatorname{single}\left(u\right) - \operatorname{single}\left(v\right))) \land (((\operatorname{a}\left(G, u, \theta\left(G, u, v\right)\right) = \frac{1}{2}) \land ((\forall (e: \mathbb{R}), ((e \in \operatorname{J}\left(G, u, v\right)) \to (0 < \operatorname{a}\left(G, u, e\right)))) \land (\sum_{e \in \operatorname{J}\left(G, u, v\right)} \operatorname{a}\left(G, u, e\right) = \frac{1}{2}))) \land ((\forall (t: \mathbb{R}), (\operatorname{U}\left(G, t, u, u\right) = \operatorname{U}\left(G, t, v, v\right))) \land (((\exists (C: \mathbb{R}), ((0 < C) \land (\forall (t: \mathbb{R}), ((0 < t) \to (C \le \left\lVert \operatorname{U}\left(G, t, u, u\right) \right\rVert))))) \Leftrightarrow (\exists (\ell: \operatorname{J}\left(G, u, v\right) \to \mathbb{Z}), ((\sum_{e \in \operatorname{J}\left(G, u, v\right)} (\ell\left(e\right): \mathbb{R}) \cdot (e - \theta\left(G, u, v\right)) = 0) \land (\operatorname{Odd}\left(\sum_{e \in \operatorname{J}\left(G, u, v\right)} \ell\left(e\right)\right))))) \land (\forall (\ell: \operatorname{J}\left(G, u, v\right) \to \mathbb{Z}), (((\sum_{e \in \operatorname{J}\left(G, u, v\right)} (\ell\left(e\right): \mathbb{R}) \cdot (e - \theta\left(G, u, v\right)) = 0) \land (\operatorname{Odd}\left(\sum_{e \in \operatorname{J}\left(G, u, v\right)} \ell\left(e\right)\right))) \to ((0 < \sum_{e \in \operatorname{J}\left(G, u, v\right)} \frac{(\ell\left(e\right): \mathbb{R})^{2}}{\operatorname{a}\left(G, u, e\right)}) \land (\forall (t: \mathbb{R}), (\frac{2}{\sum_{e \in \operatorname{J}\left(G, u, v\right)} \frac{(\ell\left(e\right): \mathbb{R})^{2}}{\operatorname{a}\left(G, u, e\right)}} \le \left\lVert \operatorname{U}\left(G, t, u, u\right) \right\rVert)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/meagher-monterde-nguyen-2026-strongly-cospectral-twins` (proved) by `D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"meagher-monterde-nguyen-2026-strongly-cospectral-twins","declaration_gid":"D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Karen Meagher, Hermie Monterde, Tung T. Nguyen (2026). *Sedentariness in Cayley graphs*. DOI: [10.48550/arXiv.2611.00567](https://doi.org/10.48550/arXiv.2611.00567). URL: <https://arxiv.org/abs/2611.00567v1>.

*Commentary.*

In the formula, theta and J denote the two definitions above. E(e) denotes the orthogonal projector onto the full eigenspace of the adjacency matrix A of G, and single(u) is the u-th coordinate vector. The weight a(G,u,e) is E(G,e) at entry (u,u). U(G,t,u,u) denotes the (u,u) entry of exp(itA). For distinct strongly cospectral twins in a finite simple graph with adjacency matrix A, the projector at the twin eigenvalue sends the first vertex vector to half the difference of the two vectors, including when the eigenvalue is repeated. The remaining weights are positive and sum to one half. Their weighted phase sum together with the twin contribution gives the diagonal of exp(itA). The projector diagonals agree at both twins, so their complex return amplitudes agree. The positive-time orbit closure recovers the qualitative equivalence in Theorem 2.2(2) of Meagher, Monterde and Nguyen. On the orbit, an odd zero-gap relation has character one, while its character at the constant phase minus one is minus one. The weighted character chord bound gives a squared displacement of four. The total weighted squared coordinate chord is twice the real part of the dephased amplitude. Each such relation gives the quantitative floor 2/D for every real time, where D is the sum of the squared integer coefficients divided by their projector weights. The gaps may be irrational, and the twins may be adjacent or nonadjacent.

The doubled independent fibers of the five-cycle give nonadjacent strongly cospectral twins. The pair differences have eigenvalue zero, and the pair-constant restriction is twice the cycle adjacency matrix. The nonzero gaps are 4, minus one plus the square root of five, and minus one minus the square root of five, with respective projector weights 1/10, 1/5, and 1/5. The irrational gap ratio rules out a positive period. The relation (1, 2, 2) gives D = 50 and a certified floor of 1/25.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound.remainingSupport`
- Truth anchor: `D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound.twinEigenvalue`
- Dependency: [D5/S3/Fourier/WeightedIntegerRelations](../../Fourier/WeightedIntegerRelations.md)
- Dependency: [D5/S3/Fourier/WeightedPhaseRelationLattice](../../Fourier/WeightedPhaseRelationLattice.md)
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees](LaplacianPeakTransferTrees.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation](StrongCospectralMultiplicityBoundRefutation.md)
