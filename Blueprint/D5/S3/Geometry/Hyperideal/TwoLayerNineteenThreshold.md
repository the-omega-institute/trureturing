# Uniform two-layer endpoint bounds

## Abstract

Exact degree threshold for uniform two-layer angle bounds.

Let b be the common low-edge upper bound and c the common high-edge upper bound, with 1<b<=2 and 1<c<=b. The independent opposite-edge endpoint is one. The low-edge and high-edge worst-case cosines are L(b,c)=(2c^2-b+1)/(2c^2+b-1) and H(b,c)=(2b^2-c+1)/(2b^2+c-1), respectively.

**Theorem 1.1 (The exact threshold).**

$$\left(\forall D \in Nat, b \in Real, c \in Real,\; \left(0 < D \land \left(D \le 18 \land \left(1 < b \land \left(b \le 2 \land \left(1 < c \land c \le b\right)\right)\right)\right)\right) \Rightarrow \left(\neg \left(\frac{\pi}{3} < arccos\left(cosine\left(b, c, c, 1, c, c\right)\right) \land \frac{2\cdot \pi}{D} < arccos\left(cosine\left(c, b, b, 1, b, b\right)\right)\right)\right)\right) \land \left(\exists b \in Real, c \in Real,\; 1 < b \land \left(b \le 2 \land \left(1 < c \land \left(c \le b \land \left(\frac{\pi}{3} < arccos\left(cosine\left(b, c, c, 1, c, c\right)\right) \land \frac{2\cdot \pi}{19} < arccos\left(cosine\left(c, b, b, 1, b, b\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/TwoLayerNineteenThreshold.exact_uniform_two_layer_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the low-edge angle arccos L(b,c) is strictly above pi/3, then H(b,c)>47/50. The three-angle cosine identity shows cos(pi/9)<47/50, so the high-edge angle is strictly below pi/9. For every positive integer D at most eighteen, pi/9 is no greater than 2pi/D. The two required strict angle inequalities therefore cannot hold together.

At degree nineteen, b=2 and c=153/125 satisfy both strict conditions. The original six-coordinate endpoint cosines are 31193/62443 and 243/257. A rigorous sine remainder bound at 22/133 and a rational upper bound for pi show that arccos(243/257)>2pi/19.

This exact threshold concerns the specified uniform two-layer endpoint estimate. It makes no assertion about other bound schemes or a hyperbolic realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/TwoLayerNineteenThreshold.exact_uniform_two_layer_threshold`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
