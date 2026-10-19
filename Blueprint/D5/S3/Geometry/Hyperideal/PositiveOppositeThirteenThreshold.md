# The common-bound scheme

## Abstract

Exact degree threshold for the positive-opposite-bound estimates.

Let a in (1,2) be the common lower bound on critical edges, and let b in (1,2) be the common upper bound on high edges. The prescribed critical lower, critical upper and high upper cosine estimates are L(a)=2(2-a)/(a+1), U(a,b)=(2b^2-a)/(1+2b^2) and H(b)=(b^3-b^2+8b+1)/(3(2b^2+1)).

**Theorem 1.1 (The first feasible high-edge degree).**

$$\left(\forall D \in Nat, a \in Real, b \in Real,\; \left(6 < D \land \left(D \le 12 \land \left(1 < a \land \left(a < 2 \land \left(1 < b \land b < 2\right)\right)\right)\right)\right) \Rightarrow \left(\neg \left(cos\left(\frac{2\cdot \pi}{6}\right) < lowBound\left(a\right) \land \left(criticalUpper\left(a, b\right) < cos\left(\frac{2\cdot \pi}{6}\right) \land highUpper\left(b\right) < cos\left(\frac{2\cdot \pi}{D}\right)\right)\right)\right)\right) \land \left(\exists a \in Real, b \in Real,\; 1 < a \land \left(a < 2 \land \left(1 < b \land \left(b < 2 \land \left(cos\left(\frac{2\cdot \pi}{6}\right) < lowBound\left(a\right) \land \left(criticalUpper\left(a, b\right) < cos\left(\frac{2\cdot \pi}{6}\right) \land highUpper\left(b\right) < cos\left(\frac{2\cdot \pi}{13}\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/PositiveOppositeThirteenThreshold.exact_positive_opposite_thirteen_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first two strict estimates at critical degree six force a<7/5 and b^2<19/10, hence b<7/5. For 1<b<7/5, the high-edge estimate H(b) exceeds H(7/5)=541/615. This is greater than cos(pi/6), which bounds cos(2pi/D) from above for every integer degree D from seven through twelve. Thus all three strict estimates cannot hold together at those degrees.

At degree thirteen the common bounds a=1399/1000 and b=689/500 satisfy all three strict estimates. The high-edge inequality follows from H(b)=176969141/199907000 and a rational lower bound for cos(44/91), with 2pi/13<44/91.

The threshold concerns these three endpoint cosine estimates. It neither constructs shared edge lengths nor proves a hyperbolic realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/PositiveOppositeThirteenThreshold.exact_positive_opposite_thirteen_threshold`
