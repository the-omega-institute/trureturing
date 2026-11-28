# The nonclique bound for a class shadow

## Abstract

Ambient deletion hypotheses imply the Appendix A edge bound on the support graph.

**Theorem 1.1 (The nonclique bound for a class shadow).**

Lean statement: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows.nonclique_shadow_edge_lower_of_ambient_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows.nonclique_shadow_edge_lower_of_ambient_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

Let t ≥ 1, w > t + 3, and let a finite ambient vertex set have at least t points. A class consists of w-subsets, and each t-subset of the ambient vertex set is disjoint from some word in the class. If the graph on ambient points whose edges are co-occurring pairs has no clique of order w + t, it has at least B(w,t) edges. The union of word supports has at least w + t points. Its induced graph has the same edges up to endpoint inclusion, retains the deletion property, and has minimum degree at least w − 1.

**Theorem 1.2 (Distance forces disjoint shadow edges).**

Lean statement: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows.shadows_edge_disjoint_of_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows.shadows_edge_disjoint_of_distance` (`✓ std3`). ∎

*Citation.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

For a finite indexed family of classes on a finite ambient vertex set, suppose all word supports have size w and the symmetric difference of supports from distinct classes has size at least 2w − 3. Then the classes' shadow edge sets are pairwise disjoint. A common edge would give two common points to supports from distinct classes, violating the distance condition.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows.nonclique_shadow_edge_lower_of_ambient_deletion`
- Truth anchor: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows.shadows_edge_disjoint_of_distance`
- Dependency: [D5/S3/Combinatorics/Graph/DeletionResilientCliques/EdgeBound](../../Graph/DeletionResilientCliques/EdgeBound.md)
