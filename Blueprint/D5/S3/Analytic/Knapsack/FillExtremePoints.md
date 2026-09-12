# Extreme feasible fills have at most one fractional row

## Abstract

Every extreme point of the finite fill feasible set has at most one strictly fractional coordinate.

Let I be any finite index type, let c(i) and d(i) be real endpoints with 0<c(i)<d(i), and let M be a real budget. Put w(i)=d(i)-c(i) and R=M-sum c(i). The feasible set F consists of functions a from I to the reals satisfying 0<=a(i)<=1 for every i and sum w(i)a(i)<=R.

**Theorem 1.1 (At most one strictly fractional coordinate).**

$$\neg \exists i, j \in I: i \neq j, 0 < \operatorname{a}\left(i\right) < 1, 0 < \operatorname{a}\left(j\right) < 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/FillExtremePoints.extreme_fill_at_most_one_fractional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a is an extreme point of F over the reals. Then there are no distinct indices i and j whose coordinates both lie strictly between zero and one. The assertion imposes no budget saturation or optimality hypothesis; if F is empty, it has no extreme points.

Suppose two such indices exist. Let delta be the minimum of w(i)a(i), w(i)(1-a(i)), w(j)a(j), and w(j)(1-a(j)). All four terms are positive. Define e(i)=delta/w(i), e(j)=-delta/w(j), and e(k)=0 at every other coordinate. The four bounds on delta keep both a+e and a-e in the unit box. Their weighted sums equal that of a because sum w(k)e(k)=0, so both points are feasible.

The point a lies in the open segment between a+e and a-e. Extremality forces a+e=a, whereas e(i)>0. This contradiction proves the claim for every finite index type, including the empty type.

## References

- Truth anchor: `D5/S3/Analytic/Knapsack/FillExtremePoints.extreme_fill_at_most_one_fractional`
- Dependency: [D5/S3/Analytic/Knapsack/GridDualStructure](GridDualStructure.md)
