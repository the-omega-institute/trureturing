# Constant lengths and constant vertex ratios on trees

## Abstract

A positive solution of the tree equations of motion on a connected tree with an edge has constant edge lengths exactly when its vertex ratios are constant.

**Theorem 1.1 (Constant lengths iff constant ratios).**

Lean statement: `D5/S3/Geometry/DiscreteGravity/TreeConstantRatios.constant_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/TreeConstantRatios.constant_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Counterexamples to Conjectures 3 and 4 of Huang, Stoica, Xia and Zhong (arXiv:2006.06716v1, Section 5.2, printed page 32)*. DOI: [10.5281/zenodo.23935004](https://doi.org/10.5281/zenodo.23935004). URL: <https://doi.org/10.5281/zenodo.23935004>.

*Commentary.*

Let g be a connected locally finite tree with at least one edge and ℓ a positive symmetric edge-length function solving the tree equations of motion of A. Huang, B. Stoica, X. Xia and X. Zhong, (R_i² + R_j²)/ℓ_ij − R_i − R_j = 0, where R_i = c_i/d_i with c_i = Σ 1/ℓ_ij and d_i = Σ 1/ℓ_ij² over the neighbours j of i. Then the edge lengths are globally constant if and only if R_i = R for every vertex and some R > 0. If every edge has length c, then c > 0, every vertex has a neighbour since the tree is connected and has an edge, and c_i = deg(i)/c, d_i = deg(i)/c² give R_i = c. If R_i = R > 0 everywhere, the edge equation reads 2R²/ℓ_ij − 2R = 0, so ℓ_ij = R. This is Corollary 5 of H. Ma and W. Zhang.

## References

- Truth anchor: `D5/S3/Geometry/DiscreteGravity/TreeConstantRatios.constant_iff`
- Dependency: [D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation](TreeEquationsNonconstantRefutation.md)
