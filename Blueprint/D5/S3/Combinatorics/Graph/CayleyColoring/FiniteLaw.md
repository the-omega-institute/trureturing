# Exact colored Cayley-tree move-count law

## Abstract

The sequential move count has the same finite law as the number of occupied ordinary bins.

**Theorem 1.1 (Count law at every positive size).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), 0<n \implies 2 \leq k \implies \forall (K: Type), \forall (e: \operatorname{Embedding}\left(\operatorname{ZMod}\left(k\right), K\right)), \forall (P: (s: \operatorname{Colored}\left(\operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(k\right)\right)) \to \operatorname{FreePolicy}\left(K, \operatorname{graph}\left(s\right)\right)), \forall (j: \mathbb{N}), \operatorname{card}\left(\operatorname{TotalNumerator}\left(e, P, j\right)\right) \cdot \operatorname{card}\left(\operatorname{Throws}\left(0, \operatorname{ZMod}\left(k\right)\right)\right) = \operatorname{frequency}\left(\operatorname{Throws}\left(0, \operatorname{ZMod}\left(k\right)\right), occupied, j\right) \cdot \operatorname{card}\left(\operatorname{SourceSample}\left(n, k\right)\right) \land 0<\operatorname{card}\left(\operatorname{SourceSample}\left(n, k\right)\right) \land 0<\operatorname{card}\left(\operatorname{Throws}\left(0, \operatorname{ZMod}\left(k\right)\right)\right) \land \operatorname{card}\left(\operatorname{Away}\left(0\right)\right) = n - 1 \land \operatorname{card}\left(\operatorname{Throw}\left(\operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(k\right)\right)\right) = n \cdot k \land (\forall (b: \operatorname{Fin}\left(n\right)), \operatorname{card}\left(\operatorname{BinFiber}\left(\operatorname{some}\left(b\right)\right)\right) = 1) \land \operatorname{card}\left(\operatorname{BinFiber}\left(none\right)\right) = n \cdot \left(k - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.native_daemon_occupancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru, and Sébastien Tixeuil (2026). *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*. DOI: [10.48550/arXiv.2611.17989](https://doi.org/10.48550/arXiv.2611.17989). URL: <https://arxiv.org/abs/2611.17989v1>.

*Commentary.*

The source numerator sums the weights of legal terminal histories at a given length over every rooted tree and initial coloring. The denominator is the number of uniform ranking and colored-tree samples. On the other side the numerator counts words with the given occupancy, and the denominator counts all marked words. The anchor is zero, and a bin survives a throw exactly when its mark in the additive color group is zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.native_daemon_occupancy`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode](CayleyCode.md)
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler](CentralScheduler.md)
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly](ForestReassembly.md)
