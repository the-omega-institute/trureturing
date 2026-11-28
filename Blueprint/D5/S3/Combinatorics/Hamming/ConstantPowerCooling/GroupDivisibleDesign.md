# Optimality from a finite design

## Abstract

A supplied uniform group divisible design attains the finite upper bound.

**Theorem 1.1 (Optimality from a finite design).**

Lean statement: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign.finite_cpecc_support_optimum_of_design`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign.finite_cpecc_support_optimum_of_design` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

Under the finite upper bound's hypotheses on n, w, t, g and k, supply a k-group divisible design on V with groups of size g. Then n(n − g)/(k(k − 1)) is the greatest attainable number of information classes. Each block supplies one class consisting of its w-subsets. It has enough points to avoid any deletion of t points, and distinct blocks share at most one point. Counting incidences in the graph of cross-group pairs gives exactly the required number of blocks.

**Definition 1.2 (A uniform group divisible design).**

Lean statement: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign.GroupDivisibleDesign`

*Formalization.* `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign.GroupDivisibleDesign` (`✓ std3`).

*Citation.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

The groups on a point set V are equivalence classes of a setoid, each of size g. The blocks form a finite family of k-subsets. A distinct pair in one group belongs to no block, and each cross-group pair belongs to exactly one block. For a finite point set of size n this is a design of type g raised to the number of groups.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign.GroupDivisibleDesign`
- Truth anchor: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign.finite_cpecc_support_optimum_of_design`
- Dependency: [D5/S3/Combinatorics/Hamming/ConstantPowerCooling/FiniteBound](FiniteBound.md)
