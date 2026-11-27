# Hu–Han Problem 6.1

## Abstract

The two sharp equality classes of signed positive square energy.

**Theorem 1.1 (Both signed square-energy equality classes).**

$$\forall n \in Nat,\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall sigma \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to Bool,\; (\operatorname{Connected}\left(G\right)) \Rightarrow (((\operatorname{sPlus}\left(G, sigma\right) = 2 \cdot \operatorname{edgeCount}\left(G\right) - n + 1) \Leftrightarrow ((\operatorname{IsTree}\left(G\right)) \lor ((\operatorname{Complete}\left(G\right)) \land (\operatorname{Balanced}\left(G, sigma\right))))) \land ((\operatorname{sPlus}\left(G, sigma\right) = n - 1) \Leftrightarrow ((\operatorname{IsTree}\left(G\right)) \lor ((\operatorname{Complete}\left(G\right)) \land (\operatorname{Antibalanced}\left(G, sigma\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SignedGraphSpectral/HuHanSquareEnergy.result` (`✓ std3`). ∎

*Resolves.* `Problems/hu-han-2026-signed-square-energy-equality` (proved) by `D5/S3/Combinatorics/SignedGraphSpectral/HuHanSquareEnergy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hu-han-2026-signed-square-energy-equality","declaration_gid":"D5/S3/Combinatorics/SignedGraphSpectral/HuHanSquareEnergy.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fu-Tao Hu and Xiao Han (2026). *From the Square-Energy Conjecture to Signed Graphs: Sharp Bounds for Positive Square Energy*. DOI: [10.48550/arXiv.2608.18492](https://doi.org/10.48550/arXiv.2608.18492). URL: <https://arxiv.org/abs/2608.18492v1>.

*Acknowledgement.* Fu-Tao Hu, Ya-Yang Liu and Yi Wang (2026). *Extremal graphs for a conjecture on the square energy of graphs*. DOI: [10.48550/arXiv.2608.17329](https://doi.org/10.48550/arXiv.2608.17329). URL: <https://arxiv.org/abs/2608.17329v1>.

*Commentary.*

Part (i) states that s⁺ = 2m − n + 1 exactly for signed trees and balanced complete graphs. Part (ii) states that s⁺ = n − 1 exactly for signed trees and antibalanced complete graphs.

Every finite vertex set can be labeled by Fin n. The signing assigns one Boolean to each unordered pair and signed adjacency uses its value only on actual edges. The positive square energy sums λ² over every strictly positive eigenvalue occurrence of that matrix. Balance and antibalance require all edge entries to be θᵢθⱼ and −θᵢθⱼ, respectively, for one vertex sign vector. These conditions describe the switching classes. The singleton has energy zero and satisfies both endpoint equalities.

Hu–Han supply the sharp bounds and the conservation identity. Hu–Liu–Wang supply the unsigned equality classifications and the normalized clique decomposition. The signed proof extends zero-sum data across blocks, uses commutation with the positive spectral part to exclude attached cliques, and recovers the switching signs on a complete graph. Conservation transfers the upper classification to the lower one under reversal of every edge sign.

## References

- Truth anchor: `D5/S3/Combinatorics/SignedGraphSpectral/HuHanSquareEnergy.result`
- Dependency: [D5/S3/Combinatorics/SignedGraphSpectral/MO479815](MO479815.md)
- Dependency: [D5/S3/Combinatorics/SignedGraphSpectral/NormalizedCliqueBlocks](NormalizedCliqueBlocks.md)
