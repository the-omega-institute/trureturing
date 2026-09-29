# Low-face neighbouring bounds

## Abstract

Uniform cosine bounds on the low-edge upper face.

The target edge occupies the first slot of the original six-coordinate cosine, and its opposite edge occupies the fourth. The four neighbouring positions are the second, third, fifth, and sixth slots. A short position has value at most 5/4. Positions remain separate even when their values or global labels coincide.

**Theorem 1.1 (Two, three, and four short positions).**

$$\forall y \in Real, z \in Real, o \in Real, v \in Real, w \in Real,\; \left(y \in Icc\left(1, 2\right) \land \left(z \in Icc\left(1, 2\right) \land \left(o \in Icc\left(1, 2\right) \land \left(v \in Icc\left(1, 2\right) \land w \in Icc\left(1, 2\right)\right)\right)\right)\right) \Rightarrow \left(\left(TwoSmall\left(y, z, v, w\right) \Rightarrow cosine\left(2, y, z, o, v, w\right) \le \frac{70}{99}\right) \land \left(\left(ThreeSmall\left(y, z, v, w\right) \Rightarrow cosine\left(2, y, z, o, v, w\right) \le \frac{49\cdot sqrt\left(6\right)}{198}\right) \land \left(\left(y \le \frac{5}{4} \land \left(z \le \frac{5}{4} \land \left(v \le \frac{5}{4} \land w \le \frac{5}{4}\right)\right)\right) \Rightarrow cosine\left(2, y, z, o, v, w\right) \le \frac{17}{33}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LowFaceNeighbourBudgets.low_face_neighbour_budgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At target value 2, with all five other coordinates in [1,2], two short neighbouring positions give cosine at most 70/99. Three short positions give at most 49sqrt(6)/198. If all four are short, the bound is 17/33.

Monotonicity raises each short neighbour to 5/4 and the others to 2, while lowering the opposite coordinate to 1. The six pair placements, four triple placements, and single quadruple placement then reduce to exact positive radicand and squared-numerator comparisons.

These bounds hold on the entire continuous upper face. They do not assert that an endpoint assignment is simultaneously realized by identified global edges.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LowFaceNeighbourBudgets.low_face_neighbour_budgets`
- Dependency: [D5/S3/Geometry/Hyperideal/CriticalTransitionStar](CriticalTransitionStar.md)
