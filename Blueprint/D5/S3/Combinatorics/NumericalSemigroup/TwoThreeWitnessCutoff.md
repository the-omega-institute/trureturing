# Optimal two-witness cutoff for the row (2, 3)

## Abstract

The minimum cutoff over two-witness spans for the degree row (2, 3).

**Theorem 1.1 (Eight is the smallest cutoff over the witness choices).**

$$\forall C \in \mathbb{Z}, (E(C) \iff \exists p,u \in \mathbb{Z}^2, p_{1} > 0 \land p_{2} > 0 \land D(u) = 1 \land (\forall t \in \mathbb{Z}, t \geq C \Rightarrow V(p,u,t)))\\E(8) \land (\forall C \in \mathbb{Z}, E(C) \Rightarrow 8 \le C)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NumericalSemigroup/TwoThreeWitnessCutoff.best_two_witness_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The degree D(x) of an integer vector x is 2x₁ + 3x₂. The predicate E(C) holds when the integer cutoff C admits one strictly positive integer vector p and one signed integer vector u of degree 1 such that every integer t ≥ C is the degree of a nonnegative vector in their integer span. Viable(p,u,t) denotes this last condition. The formula writes it as V(p,u,t).

For a cutoff at most seven, choose vectors of degrees 7, 8, 9 and 10 in the same span. The absolute determinant of the witnesses is at least two since the entries of u have opposite signs. It divides the determinant of every pair of vectors in the span. The nonnegative solutions at the four degrees force the determinant to have absolute value two. This forces u = (−1, 1). The unique vector (2, 1) of degree 7 has determinant 3 with that u, giving a contradiction.

With p = (1, 1) and u = (−1, 1), write t = 8 + 4q + r with q ≥ 0 and 0 ≤ r < 4. The vector (4 + 2q − r, r) has degree t and is an integer combination of the two witnesses. Thus eight is attained.

## References

- Truth anchor: `D5/S3/Combinatorics/NumericalSemigroup/TwoThreeWitnessCutoff.best_two_witness_cutoff`
