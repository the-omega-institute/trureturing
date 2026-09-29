# High-face neighbouring bounds

## Abstract

High-face cosine bounds for each neighbouring colour count.

The target edge occupies the first of six local positions. The second, third, fifth, and sixth positions are its four neighbours. Each Boolean colour records whether that position is high. Equal lengths or repeated global edges still contribute separately to the count.

**Theorem 1.1 (Five bounds indexed by the high-neighbour count).**

$$\forall bY \in Bool, bZ \in Bool, bV \in Bool, bW \in Bool, y \in Real, z \in Real, o \in Real, v \in Real, w \in Real,\; \left(y \in Icc\left(1, if\left(bY, \frac{5}{4}, 2\right)\right) \land \left(z \in Icc\left(1, if\left(bZ, \frac{5}{4}, 2\right)\right) \land \left(o \in Icc\left(1, 2\right) \land \left(v \in Icc\left(1, if\left(bV, \frac{5}{4}, 2\right)\right) \land w \in Icc\left(1, if\left(bW, \frac{5}{4}, 2\right)\right)\right)\right)\right)\right) \Rightarrow cosine\left(\frac{5}{4}, y, z, o, v, w\right) \le q\left(highCount\left(bY, bZ, bV, bW\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/HighFaceNeighbourBudgets.high_face_neighbour_budgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At target value 5/4, each high neighbour lies in [1,5/4], each low neighbour lies in [1,2], and the opposite coordinate lies in [1,2]. For zero through four high neighbours, the respective cosine upper bounds are 31/33, 25/sqrt(726), 81/88, 61/sqrt(4752), and 23/27.

Coordinate monotonicity raises each neighbour to its colour endpoint and lowers the opposite coordinate to 1. All sixteen labelled colour patterns satisfy the appropriate positive-radicand squared comparison, including the three distinct placements with two high neighbours.

The bounds hold throughout the continuous upper face. No endpoint realization by a face pairing is assumed.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/HighFaceNeighbourBudgets.high_face_neighbour_budgets`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
