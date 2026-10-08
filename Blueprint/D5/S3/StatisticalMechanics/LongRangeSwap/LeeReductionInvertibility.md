# Lee's reduction operators are invertible

## Abstract

Every reduction operator is a unit for all species counts, word lengths, valid block positions, and parameters in the closed unit cube.

**Definition 1.1 (Lee's reduction recursion).**

$$\forall N \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall j \in \mathbb{N},\; \operatorname{A}\left(N, n, mu, j, 0\right) = 1 \land (\forall k \in \mathbb{N},\; \operatorname{A}\left(N, n, mu, j, k + 1\right) = 1 - \operatorname{LeeCollisionExit}.\operatorname{calB}\left(N, n, mu, j, k + 2\right) \cdot (\operatorname{A}\left(N, n, mu, j, k\right))^{-1} \cdot \operatorname{LeeCollisionExit}.\operatorname{calBprime}\left(N, n, mu, j, k + 1\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeReductionInvertibility.A` (`✓ std3`).

*Citation.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

Equation (28), source label 1122am331, defines A zero as the identity and the next A by the displayed matrix-inverse recursion. The carrier is Matrix (Fin n to Fin N) (Fin n to Fin N) over the reals; 1 denotes its identity matrix. Implicit sizes N and n are shown explicitly.

**Definition 1.2 (Lee's invertibility conjecture).**

$$claim = \left(\forall N \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall k \in \mathbb{N},\; (1 \le N) \Rightarrow ((2 \le n) \Rightarrow ((1 \le j) \Rightarrow ((j + k + 1 \le n) \Rightarrow (\forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; (\forall a \in \operatorname{Fin}\left(N\right),\; 0 \le mu\left(a\right) \land (mu\left(a\right) \le 1)) \Rightarrow (\operatorname{IsUnit}\left(\operatorname{A}\left(N, n, mu, j, k\right)\right))))))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeReductionInvertibility.claim` (`✓ std3`).

*Citation.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

Remark 3.1, page 18: These results lead us to conjecture that 𝔄_k is invertible for all parameters μ_i ∈ [0,1]. The encoding quantifies over every N at least one, n at least two, one-indexed block start j at least one, and k with j + k + 1 at most n. Species are Fin N; words are Fin n to Fin N; invertibility means IsUnit of the full word-coordinate matrix. The parameters include the endpoints zero and one.

**Theorem 1.3 (Proof of invertibility on the entire parameter cube).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/LongRangeSwap/LeeReductionInvertibility.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

Positive-weight collision paths reach the absorbing boundary in at most 2 N m steps. The two outgoing masses sum to one on each interior row. The attained-maximum principle forces every zero-boundary harmonic block chain to vanish. Extending a vector backwards through the already invertible pivots and using uniqueness proves the next pivot has zero kernel, hence is a unit. Induction identifies these pivots with the literal reduction recursion. The stochastic walk includes absorbing boundary rows; its restriction to interior rows is substochastic.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeReductionInvertibility.A`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeReductionInvertibility.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeReductionInvertibility.result`
- Dependency: [D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit](LeeCollisionExit.md)
- Dependency: [D5/S3/StatisticalMechanics/RandomWalks/FiniteBinaryDirichletMaximum](../RandomWalks/FiniteBinaryDirichletMaximum.md)
