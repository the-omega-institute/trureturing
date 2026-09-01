# One-Step Memory Unique Naming

## Abstract

Gapless unique weighting of one-step binary names forces Fibonacci weights and growth.

**Theorem 1.1 (Unique seamless one-step naming forces Fibonacci growth).**

$$\begin{gathered}\forall weight, B: \mathbb{N} \to \mathbb{N},\\{}\forall n \in \mathbb{N},\; \operatorname{BijOn}\left((name: \operatorname{GoldenName}\left(n\right) \mapsto \sum_{k \in name} weight\left(k\right)), \operatorname{univ}\left(\operatorname{GoldenName}\left(n\right)\right), \left\{v < B\left(n\right) \mid v \in \mathbb{N}\right\}\right) \Rightarrow\\{}\forall n \in \mathbb{N},\; weight\left(n + 2\right) = \operatorname{Fib}\left(n + 2\right) \land\\{}\forall n \in \mathbb{N},\; B\left(n\right) = \operatorname{Fib}\left(n + 2\right) \land\\{}\operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \frac{(B\left(n + 1\right) : \mathbb{R})}{(B\left(n\right) : \mathbb{R})}), atTop, \operatorname{nhds}\left(\varphi\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/OneStepMemoryUniqueNaming.one_step_memory_unique_naming` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

GoldenName(n) is the canonical carrier of length-n binary words with no adjacent occupied positions. The weight function is indexed by its canonical Fibonacci indices, so source weight a_m is weight(m+1).

The hypothesis says that the actual weighted-sum map is bijective from the whole canonical name layer onto the initial interval below B(n). It therefore includes both uniqueness and gapless coverage.

Layer cardinality first forces B(n)=Fib(n+2). Comparing the old layer with the new singleton at index n+2 then forces its weight to equal B(n). The pinned Fibonacci ratio limit supplies the final golden growth rate.

## References

- Truth anchor: `D5/S0/Tower/OneStepMemoryUniqueNaming.one_step_memory_unique_naming`
- Dependency: [D5/S0/Tower/GoldenNames](GoldenNames.md)
