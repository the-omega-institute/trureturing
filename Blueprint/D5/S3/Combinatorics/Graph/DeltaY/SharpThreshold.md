# Zhou's sharp degree-six threshold

## Abstract

Six is the least minimum-degree threshold at which ordinary and strong reachability agree up to graph isomorphism.

**Definition 1.1 (Equality of reachable families).**

Lean statement: `D5/S3/Combinatorics/Graph/DeltaY/SharpThreshold.P`

*Formalization.* `D5/S3/Combinatorics/Graph/DeltaY/SharpThreshold.P` (`✓ std3`).

*Citation.* Zhichen Zhou (2026). *Δ-Y Moves and Partial Steiner Systems*. DOI: [10.48550/arXiv.2609.08963](https://doi.org/10.48550/arXiv.2609.08963). URL: <https://arxiv.org/html/2609.08963v1>.

*Commentary.*

P(d) says that for every finite simple graph with every vertex of degree at least d, ordinary and strong finite histories reach the same family of graphs up to isomorphism.

**Theorem 1.2 (The exact threshold).**

$$\operatorname{P}\left(6\right) \land (\forall d \in Nat,\; d < 6 \Rightarrow \left(\neg \operatorname{P}\left(d\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DeltaY/SharpThreshold.zhou_sharp_threshold` (`✓ std3`). ∎

*Resolves.* `Problems/zhou-strong-reverse-degree-six` (proved) by `D5/S3/Combinatorics/Graph/DeltaY/SharpThreshold.zhou_sharp_threshold`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhou-strong-reverse-degree-six","declaration_gid":"D5/S3/Combinatorics/Graph/DeltaY/SharpThreshold.zhou_sharp_threshold","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zhichen Zhou (2026). *Δ-Y Moves and Partial Steiner Systems*. DOI: [10.48550/arXiv.2609.08963](https://doi.org/10.48550/arXiv.2609.08963). URL: <https://arxiv.org/html/2609.08963v1>.

*Commentary.*

The two-color invariant makes every reachable reverse move strong when the starting graph has minimum degree at least six.

Start with the complete graph on 0 through 6 and remove the pairs 06 and 14. Perform forward moves on 012 at 7 and 034 at 8, reverse at 0, perform a forward move on 157 at 9, then reverse at 1.

The last center has neighbors 3, 6 and 9, with just the pair 36 already present. Its removal lowers the edge count from 19 to 18. Strong histories and graph isomorphisms preserve edge count, so the endpoint separates the two reachable families at every threshold below six.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DeltaY/SharpThreshold.P`
- Truth anchor: `D5/S3/Combinatorics/Graph/DeltaY/SharpThreshold.zhou_sharp_threshold`
- Dependency: [D5/S3/Combinatorics/Graph/DeltaY/TwoColorInvariant](TwoColorInvariant.md)
