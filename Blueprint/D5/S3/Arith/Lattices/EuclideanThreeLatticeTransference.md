# Euclidean three-dimensional lattice transference

## Abstract

A fixed nonzero integral-dual vector controls every covering error in dimension three.

**Theorem 1.1 (Squared covering error times squared dual length is at most eleven twelfths).**

$$\forall L: \operatorname{Submodule}\left(\mathbb{Z}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)\right), [\operatorname{DiscreteTopology}\left(L\right)] [\operatorname{IsZLattice}\left(\mathbb{R}, L\right)], \exists y \in \operatorname{dualSubmodule}\left(\left(\operatorname{inner}_{l}\right)\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)\right), L\right), y \neq 0 \land (\forall x: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \exists v \in L, \left\lVert x - v \right\rVert^{2} \cdot \left\lVert y \right\rVert^{2} \le \frac{11}{12})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference.exists_dual_covering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dual submodule is taken with respect to the real inner product on EuclideanSpace ℝ (Fin 3). The membership condition says that the inner product with every element of L is integral. The proof chooses y once for L, before the target x is given.

Project successively off shortest nonzero vectors a and b in the first two lattices. A shortest generator c of the last image yields the integral-dual vector y = c/‖c‖². Rounding along the last direction costs at most ‖c‖²/4 in squared distance. A reduced planar circumradius estimate bounds the squared perpendicular correction by ‖b‖²/2. Projection separation gives ‖c‖² ≥ 3‖b‖²/4, so the total squared error is at most (11/12)‖c‖². The squared dual length is 1/‖c‖².

The formal proof uses shortest-vector projection. The independent geometry-of-numbers derivation in Pro receipt e5e86a56-5405-4540-a08f-501fa628496f supplies the reduced planar circumradius argument and the resulting three-dimensional constant.

## References

- Truth anchor: `D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference.exists_dual_covering`
