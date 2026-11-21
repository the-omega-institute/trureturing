# Compactly supported quadratic tails

## Abstract

Sharpness for monotone counting tails

**Theorem 1.1 (A monotone count with quadratic depth and cubic mass).**

$$\forall s \in \mathbb{R},\; \left(0 < s \land s \le \frac{1}{2}\right) \Rightarrow \left(\exists A \in \mathbb{R}\to\mathbb{R},\; \operatorname{Monotone}\left(A\right) \land \left(\left(\forall t \in \mathbb{R},\; 1 \le t \Rightarrow 0 \le \operatorname{A}\left(t\right)\right) \land \left(\left(\forall t \in \mathbb{R},\; \left(t < 2-s \lor 2+s < t\right) \Rightarrow \operatorname{A}\left(t\right) = t\right) \land \left(\operatorname{Integrable}\left(K\right) \land \left(\operatorname{Q}\left(2\right) = -\frac{s^{2}}{32} \land N \le \frac{s^{3}}{16}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MonotoneTailSharpness.monotone_tail_quadratic_depth_cubic_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real integrable kernel K is (A(t)−t)/t². Write Q(z) for its tail integral from z to infinity and N for the integral of max(−Q(z),0)/√z from 1 to 3.

Use A(t)=t−t²(t−2)/16 for 2−s<t≤2+s and A(t)=t elsewhere. The polynomial is nondecreasing on [3/2,5/2]. At the lower cutoff its value is at least 2−s. At the upper cutoff it is at most 2+s. These comparisons preserve monotonicity across both joins.

The kernel equals (2−t)/16 on the window and vanishes outside it. Its tail therefore vanishes outside the closed window and equals ((z−2)²−s²)/32 within it. In particular the value at 2 is −s²/32. The negative part is bounded by s²/32 on a set of length 2s, where 1/√z≤1, so N≤s³/16.

Let s tend to zero. A depth bound C times the window mass to the power α cannot hold uniformly over these monotone counts when α>2/3. The construction uses the real monotone count class. The extra arithmetic structure of the Chebyshev prime count remains relevant to any stronger bound there.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MonotoneTailSharpness.monotone_tail_quadratic_depth_cubic_mass`
