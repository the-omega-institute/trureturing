# An infinite twin-free theta separating family

## Abstract

An infinite twin-free theta separating family.

**Definition 1.1 (The infinite-family question).**

$$\operatorname{claim} = \exists orders: \operatorname{Nat} \to \operatorname{Nat}, \exists graphs: (i: \operatorname{Nat}) \to \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(orders\left(i\right)\right)\right), (\forall i: \operatorname{Nat}, ((graphs\left(i\right)).\operatorname{Connected}) \land ((\operatorname{TwinFree}\left(graphs\left(i\right)\right)) \land (((\operatorname{mmL}\left(graphs\left(i\right)\right) = \operatorname{metricDimension}\left(graphs\left(i\right)\right)) \land (\operatorname{mmQ}\left(graphs\left(i\right)\right) \ne \operatorname{metricDimension}\left(graphs\left(i\right)\right))) \lor ((\operatorname{mmQ}\left(graphs\left(i\right)\right) = \operatorname{metricDimension}\left(graphs\left(i\right)\right)) \land (\operatorname{mmL}\left(graphs\left(i\right)\right) \ne \operatorname{metricDimension}\left(graphs\left(i\right)\right)))))) \land (\forall i: \operatorname{Nat}, \forall j: \operatorname{Nat}, (i \ne j) \Rightarrow (\neg (\operatorname{Nonempty}\left((graphs\left(i\right)).\operatorname{Iso}\left(graphs\left(j\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaSeparation.claim` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Problem 30 (p. 27): “Do there exist infinite families of connected twin-free graphs satisfying exactly one of the two equalities mm_L(G)=dim(G), mm_Q(G)=dim(G)? The computational census shows that finite twin-free examples occur in both directions.” The carrier of graph i is Fin (orders i). Pairwise nonisomorphism expresses infinitude; the disjunction allows either equality direction in each member.

**Theorem 1.2 (An infinite separating family).**

$$\exists orders: \operatorname{Nat} \to \operatorname{Nat}, \exists graphs: (i: \operatorname{Nat}) \to \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(orders\left(i\right)\right)\right), (\forall i: \operatorname{Nat}, ((graphs\left(i\right)).\operatorname{Connected}) \land ((\operatorname{TwinFree}\left(graphs\left(i\right)\right)) \land (((\operatorname{mmL}\left(graphs\left(i\right)\right) = \operatorname{metricDimension}\left(graphs\left(i\right)\right)) \land (\operatorname{mmQ}\left(graphs\left(i\right)\right) \ne \operatorname{metricDimension}\left(graphs\left(i\right)\right))) \lor ((\operatorname{mmQ}\left(graphs\left(i\right)\right) = \operatorname{metricDimension}\left(graphs\left(i\right)\right)) \land (\operatorname{mmL}\left(graphs\left(i\right)\right) \ne \operatorname{metricDimension}\left(graphs\left(i\right)\right)))))) \land (\forall i: \operatorname{Nat}, \forall j: \operatorname{Nat}, (i \ne j) \Rightarrow (\neg (\operatorname{Nonempty}\left((graphs\left(i\right)).\operatorname{Iso}\left(graphs\left(j\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaSeparation.result` (`✓ std3`). ∎

*Resolves.* `Problems/aks2610` (proved) by `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaSeparation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"aks2610","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaSeparation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Take orders i=6(i+1)+9 and graphs i=thetaGraph (6(i+1)+4). Every graph is connected and twin-free, its metric dimension and Laplacian maximum multiplicity equal 2, and its signless maximum multiplicity is at most 1. Distinct orders exclude isomorphisms.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaSeparation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaSeparation.result`
- Dependency: [D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation](../Graph/SubgroupGenerating/CyclicExtensionRefutation.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/BonettoSignature](BonettoSignature.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence](TwinFreeThetaRecurrence.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure](TwinFreeThetaStructure.md)
