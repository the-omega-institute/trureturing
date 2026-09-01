# Projective Primal Convergence

## Abstract

Finite circle-moment primal optima converge to the full determining-family value by weak-star compactness and closedness.

**Theorem 1.1 (Mass-bounded circle measures have a weak-star convergent subsequence).**

$$\forall C \in \operatorname{NNReal}\left(\right), mu \in \operatorname{Nat}\left(\right) \to \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right),\; \left(\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{mass}\left(\operatorname{apply}\left(mu, n\right)\right) \le C\right) \Rightarrow \left(\exists muStar \in \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right), phi \in \operatorname{Nat}\left(\right) \to \operatorname{Nat}\left(\right),\; \operatorname{mass}\left(muStar\right) \le C \land \left(\operatorname{StrictMono}\left(phi\right) \land \operatorname{Tendsto}\left((k\mapsto\operatorname{apply}\left(mu, \operatorname{apply}\left(phi, k\right)\right)), atTop, \operatorname{nhds}\left(muStar\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/ProjectivePrimalConvergence.mass_bounded_weakStar_subsequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof extracts total masses in a compact interval and normalized probability measures in their compact metrizable weak topology, then reconstructs the finite-measure limit by continuous scalar multiplication.

**Theorem 1.2 (The common primal budget box is weak-star compact).**

$$\forall C \in \operatorname{NNReal}\left(\right),\; \operatorname{IsCompact}\left(\operatorname{commonFeasible}\left(C\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/ProjectivePrimalConvergence.commonFeasible_isCompact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both the Haar coefficient interval and the mass-bounded residual-measure set are compact, so their product is compact.

**Theorem 1.3 (Finite-level primal feasible sets are weak-star closed).**

$$\forall C \in \operatorname{NNReal}\left(\right), Gamma \in \operatorname{Nat}\left(\right) \to \operatorname{ContinuousMap}\left(\operatorname{Circle}\left(\right), \operatorname{Real}\left(\right)\right), w \in \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right), N \in \operatorname{Nat}\left(\right),\; \operatorname{IsClosed}\left(\operatorname{levelFeasible}\left(C, Gamma, w, N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/ProjectivePrimalConvergence.levelFeasible_isClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reconstruction mass cap and every finite moment equality are closed because mass and integration against continuous circle functions are continuous in the weak topology.

**Theorem 1.4 (Every finite level has a primal optimizer).**

$$\forall C \in \operatorname{NNReal}\left(\right), Gamma \in \operatorname{Nat}\left(\right) \to \operatorname{ContinuousMap}\left(\operatorname{Circle}\left(\right), \operatorname{Real}\left(\right)\right), w \in \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right), N \in \operatorname{Nat}\left(\right),\; \operatorname{Nonempty}\left(\operatorname{fullFeasible}\left(C, Gamma, w\right)\right) \Rightarrow \left(\exists pStar \in \operatorname{Prod}\left(\operatorname{NNReal}\left(\right), \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right)\right),\; \operatorname{Mem}\left(pStar, \operatorname{levelFeasible}\left(C, Gamma, w, N\right)\right) \land \left(\forall p \in \operatorname{Prod}\left(\operatorname{NNReal}\left(\right), \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right)\right),\; \operatorname{Mem}\left(p, \operatorname{levelFeasible}\left(C, Gamma, w, N\right)\right) \Rightarrow \operatorname{objective}\left(p\right) \le \operatorname{objective}\left(pStar\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/ProjectivePrimalConvergence.level_optimizer_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full feasibility makes every finite level nonempty; the continuous Haar-floor coordinate therefore attains its maximum on the compact level set.

**Theorem 1.5 (Circle primal frontiers decrease to the full frontier).**

$$\forall C \in \operatorname{NNReal}\left(\right), Gamma \in \operatorname{Nat}\left(\right) \to \operatorname{ContinuousMap}\left(\operatorname{Circle}\left(\right), \operatorname{Real}\left(\right)\right), w \in \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right),\; \operatorname{Nonempty}\left(\operatorname{fullFeasible}\left(C, Gamma, w\right)\right) \Rightarrow \left(\operatorname{Antitone}\left(\operatorname{levelFrontier}\left(C, Gamma, w\right)\right) \land \left(\operatorname{Tendsto}\left(\operatorname{levelFrontier}\left(C, Gamma, w\right), atTop, \operatorname{nhds}\left(\operatorname{fullFrontier}\left(C, Gamma, w\right)\right)\right) \land \left(\exists optimizer \in \operatorname{Nat}\left(\right) \to \operatorname{Prod}\left(\operatorname{NNReal}\left(\right), \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right)\right), cluster \in \operatorname{Prod}\left(\operatorname{NNReal}\left(\right), \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right)\right), phi \in \operatorname{Nat}\left(\right) \to \operatorname{Nat}\left(\right),\; \left(\forall N \in \operatorname{Nat}\left(\right),\; \operatorname{Mem}\left(\operatorname{apply}\left(optimizer, N\right), \operatorname{levelFeasible}\left(C, Gamma, w, N\right)\right)\right) \land \left(\operatorname{StrictMono}\left(phi\right) \land \left(\operatorname{Tendsto}\left((k\mapsto\operatorname{apply}\left(optimizer, \operatorname{apply}\left(phi, k\right)\right)), atTop, \operatorname{nhds}\left(cluster\right)\right) \land \left(\operatorname{Mem}\left(cluster, \operatorname{fullFeasible}\left(C, Gamma, w\right)\right) \land \operatorname{objective}\left(cluster\right) = \operatorname{fullFrontier}\left(C, Gamma, w\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/ProjectivePrimalConvergence.projective_primal_convergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite-level optimizers lie in one weak-star compact budget box. A convergent subsequence is extracted rather than supplied as a premise.

Closedness transfers the reconstruction budget and each fixed determining moment to the cluster, proving full feasibility. Continuity of the Haar-floor coordinate then identifies the antitone value limit with the full optimum.

## References

- Truth anchor: `D5/S3/Weil/Budget/ProjectivePrimalConvergence.commonFeasible_isCompact`
- Truth anchor: `D5/S3/Weil/Budget/ProjectivePrimalConvergence.levelFeasible_isClosed`
- Truth anchor: `D5/S3/Weil/Budget/ProjectivePrimalConvergence.level_optimizer_exists`
- Truth anchor: `D5/S3/Weil/Budget/ProjectivePrimalConvergence.mass_bounded_weakStar_subsequence`
- Truth anchor: `D5/S3/Weil/Budget/ProjectivePrimalConvergence.projective_primal_convergence`
- Dependency: [D5/S3/Weil/Budget/FullCirclePrimalAttainment](FullCirclePrimalAttainment.md)
