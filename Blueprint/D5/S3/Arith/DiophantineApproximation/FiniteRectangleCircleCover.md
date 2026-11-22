# Finite rectangular circle-cover inverse

## Abstract

A missed open phase window on a closed integer rectangle forces a positive simultaneous resonance.

**Theorem 1.1 (A joint squared resonance bound of eleven thirds).**

$$\forall N, M: \mathbb{N}, 2 \le N \to 2 \le M \to \forall \theta, \phi, t, w: \mathbb{R}, (0 < w \land w < 1) \to \neg (\exists b, d: \mathbb{N}, \exists a: \mathbb{Z}, N \le b \land b \le 2 \cdot N \land M \le d \land d \le 2 \cdot M \land t < (b : \mathbb{R}) \cdot \theta + (d : \mathbb{R}) \cdot \phi - (a : \mathbb{R}) \land (b : \mathbb{R}) \cdot \theta + (d : \mathbb{R}) \cdot \phi - (a : \mathbb{R}) < t + w) \to \exists h, j, k: \mathbb{Z}, 1 \le h \land (N : \mathbb{R})^{2} \cdot \left((h : \mathbb{R}) \cdot \theta - (j : \mathbb{R})\right)^{2} + (M : \mathbb{R})^{2} \cdot \left((h : \mathbb{R}) \cdot \phi - (k : \mathbb{R})\right)^{2} + w^{2} \cdot (h : \mathbb{R})^{2} \le \frac{11}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DiophantineApproximation/FiniteRectangleCircleCover.finite_rectangle_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rectangular constraints include their integer endpoints. The phase window is open, and the phases may be rational. Each natural or integer variable in a real expression is explicitly cast to ℝ in the formula.

The lattice points are (b/N, d/M, (bθ + dφ − a)/w) for integers b, d, a. A point at Euclidean distance less than 1/2 from (3/2, 3/2, (t + w/2)/w) would hit the rectangle and window. The covering bound at this center gives a squared dual length at most 4·(11/12) = 11/3. `D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference.exists_dual_covering`

The dual coordinates are (N(j − hθ), M(k − hφ), wh) with integer h, j, k. Because N and M are at least 2 and 11/3 < 4, h = 0 would force j = k = 0. Changing the signs of all three integers when h is negative gives h ≥ 1 and preserves the joint bound.

The triangular-lattice reduction and joint constant are also derived in Pro receipt e5e86a56-5405-4540-a08f-501fa628496f.

## References

- Truth anchor: `D5/S3/Arith/DiophantineApproximation/FiniteRectangleCircleCover.finite_rectangle_inverse`
- Truth anchor: `D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference.exists_dual_covering`
- Dependency: [D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference](../Lattices/EuclideanThreeLatticeTransference.md)
