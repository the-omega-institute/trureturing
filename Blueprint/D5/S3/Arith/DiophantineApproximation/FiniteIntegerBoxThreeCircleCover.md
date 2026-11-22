# Finite three-axis integer-box inverse

## Abstract

A missed strict phase window on a closed three-axis integer box forces a positive simultaneous resonance.

**Theorem 1.1 (A padded joint squared resonance bound of 43/9).**

$$\forall N: \operatorname{Fin}\left(3\right) \to \mathbb{Z}, (\forall i: \operatorname{Fin}\left(3\right), 1 \le N_{i}) \to \forall \theta: \operatorname{Fin}\left(3\right) \to \mathbb{R}, \forall t, w: \mathbb{R}, 0 < w \to \neg (\exists b: \operatorname{Fin}\left(3\right) \to \mathbb{Z}, \exists m: \mathbb{Z}, (\forall i: \operatorname{Fin}\left(3\right), N_{i} \le b_{i} \land b_{i} \le 2 \cdot N_{i}) \land t < \sum_{i \in \operatorname{Fin}\left(3\right)} ((b_{i} : \mathbb{R}) \cdot \theta_{i}) - (m : \mathbb{R}) \land \sum_{i \in \operatorname{Fin}\left(3\right)} ((b_{i} : \mathbb{R}) \cdot \theta_{i}) - (m : \mathbb{R}) < t + w) \to \exists h: \mathbb{Z}, \exists j: \operatorname{Fin}\left(3\right) \to \mathbb{Z}, 1 \le h \land \sum_{i \in \operatorname{Fin}\left(3\right)} (\left((N_{i} : \mathbb{R}) + 2\right)^{2} \cdot \left((h : \mathbb{R}) \cdot \theta_{i} - (j_{i} : \mathbb{R})\right)^{2}) + w^{2} \cdot (h : \mathbb{R})^{2} \le \frac{43}{9}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DiophantineApproximation/FiniteIntegerBoxThreeCircleCover.finite_integer_box_inverse_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set Rᵢ = Nᵢ + 2. The triangular lattice has three coordinates bᵢ/Rᵢ and fourth coordinate (∑ᵢ bᵢθᵢ − m)/w. Use the center with axis coordinates 3Nᵢ/(2Rᵢ) and fourth coordinate (t + w/2)/w. A point at distance less than 1/2 would give Nᵢ − 1 < bᵢ < 2Nᵢ + 1 on each axis. Integrality includes both endpoints Nᵢ and 2Nᵢ, and the fourth coordinate gives a strict phase hit.

The missed window therefore bounds the distance to each lattice point below by 1/2. At the center the four-dimensional covering bound gives a nonzero integral-dual vector of squared length at most 4·(43/36) = 43/9. `D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference.exists_dual_covering_four`

The dual coordinates are Rᵢ(jᵢ − hθᵢ) and wh. If h were zero, any nonzero jᵢ would give a squared coordinate at least Rᵢ² ≥ 9, which exceeds 43/9. Since the dual vector is nonzero, h is nonzero. Reversing the common sign if needed yields h ≥ 1 with the same norm.

## References

- Truth anchor: `D5/S3/Arith/DiophantineApproximation/FiniteIntegerBoxThreeCircleCover.finite_integer_box_inverse_three`
- Truth anchor: `D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference.exists_dual_covering_four`
- Dependency: [D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference](../Lattices/EuclideanThreeLatticeTransference.md)
