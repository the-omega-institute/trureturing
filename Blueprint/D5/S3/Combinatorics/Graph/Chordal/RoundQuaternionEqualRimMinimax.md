# Cyclic equal-rim quaternion minimax

## Abstract

The cyclic equal-rim assignment has an exact minimax fit at every angle. Its ratio of fit radius to positive triangle defect has a unique maximum at the quarter turn.

Write S for the group of unit real quaternions with round distance given by the arccosine of the real inner product. The four vertices are 0, 1, 2, and 3. The assignment G has identity gain on the diagonal and on every spoke to and from 0. The edges 12, 23, and 31 have gain given by the cosine of the angle plus its sine times the unit imaginary quaternion. Their reverse gains are inverses. The predicate D requires inverse reversal, identity diagonal, and a bound on the distance from each two-edge triangle product to the direct gain. The predicate F bounds the distance from each directed gain to the product of the inverse potential at its source and the potential at its target.

The defect e is three times the angle up to pi over three. From there to pi over two it is two pi minus three times the angle. For larger angles it equals the angle. The radius R equals the angle up to pi over three. For larger angles it is the arccosine of the positive quadratic root. The quadratic coefficient is the difference between the cosine of the angle displaced by two pi over three and the cosine of the angle. The linear coefficient is one and the constant coefficient is the negative of the displaced cosine.

**Theorem 1.1 (Exact triangle defect and minimax radius).**

$$\forall I \in \mathbb{H},\; (\operatorname{re}\left(I\right) = 0) \Rightarrow ((\operatorname{norm}\left(I\right) = 1) \Rightarrow (\forall a \in \mathbb{R},\; ((0 \leq a) \land (a \leq \pi)) \Rightarrow ((\operatorname{D}\left(\operatorname{G}\left(I, a\right), \operatorname{e}\left(a\right)\right)) \land ((\forall d \in \mathbb{R},\; (\operatorname{D}\left(\operatorname{G}\left(I, a\right), d\right)) \Rightarrow (\operatorname{e}\left(a\right) \leq d)) \land ((\exists p \in \operatorname{Fin}\left(4\right) \to S,\; \operatorname{F}\left(\operatorname{G}\left(I, a\right), p, \operatorname{R}\left(a\right)\right)) \land (\forall p \in \operatorname{Fin}\left(4\right) \to S,\; \forall r \in \mathbb{R},\; (\operatorname{F}\left(\operatorname{G}\left(I, a\right), p, r\right)) \Rightarrow (\operatorname{R}\left(a\right) \leq r)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionEqualRimMinimax.equalRim_exact_defect_and_minimax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spoke and rim triangles have principal angles given by the common rim angle and the angle of its cube. After left translation sets the hub potential to one, the spokes bound the projection of the rim mean. Subtracting that mean leaves a cyclic symmetric sum equal to minus half the centered energy and a cyclic skew sum bounded by the square root of three times half that energy. Combining both sums bounds the average rim score and gives the quadratic constraint on any positive common edge score. A constant potential attains the small-angle bound. An equilateral triangle at the latitude of the positive root attains the large-angle bound.

**Theorem 1.2 (Unique maximum of the minimax-to-defect ratio).**

$$\forall a \in \mathbb{R},\; ((0 < a) \land (a \leq \pi)) \Rightarrow ((\frac{\operatorname{R}\left(a\right)}{\operatorname{e}\left(a\right)} \leq \frac{2 \cdot \operatorname{arccos}\left(\frac{1}{\sqrt{3}}\right)}{\pi}) \land ((\frac{\operatorname{R}\left(a\right)}{\operatorname{e}\left(a\right)} = \frac{2 \cdot \operatorname{arccos}\left(\frac{1}{\sqrt{3}}\right)}{\pi}) \Leftrightarrow (a = \frac{\pi}{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionEqualRimMinimax.equalRim_ratio_unique_maximum_at_quarter_turn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The small-angle ratio is one third. At latitude one over the square root of three the common rim score is the sine of the angle times the latitude. This bounds the radius by a convex arccosine function of the distance from the quarter turn. Its secant bound increases strictly more slowly than the scaled defect away from the quarter turn. At the quarter turn the fixed latitude is the optimal quadratic root.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionEqualRimMinimax.equalRim_exact_defect_and_minimax`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionEqualRimMinimax.equalRim_ratio_unique_maximum_at_quarter_turn`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds](RoundQuaternionK4Bounds.md)
