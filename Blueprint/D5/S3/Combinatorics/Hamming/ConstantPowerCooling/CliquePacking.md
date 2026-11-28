# Degrees in a clique packing

## Abstract

Degrees and incidences count a packing of fixed-size cliques.

**Theorem 1.1 (Degrees in a clique packing).**

Lean statement: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking.packedGraph_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking.packedGraph_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

For a finite indexed family of k-element blocks in which distinct blocks meet in at most one point, the degree of any point in the graph of covered pairs is (k − 1) times the number of blocks through it. The other points in the blocks through a point form pairwise disjoint neighbor sets.

**Theorem 1.2 (Total block incidence).**

Lean statement: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking.incidence_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking.incidence_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

For a finite indexed family of k-element blocks on a finite set, the sum of the numbers of incident blocks over points is k times the number of blocks. The two sums count the same point–block incidences.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking.incidence_sum`
- Truth anchor: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking.packedGraph_degree`
