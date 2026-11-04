# Quantitative Rotation Hitting

## Abstract

Explicit badly-approximable estimates and uniform finite hitting for scaled square-root rotations.

All phases are real numbers with their integer lifts retained. Natural numbers and rounded integers in real expressions denote their canonical real coercions. Int.fract is the representative in [0,1). Mathlib supplies irrational_sqrt_two, nearest-integer rounding and the Dirichlet return theorem Real.exists_nat_abs_mul_sub_round_le. The quantitative construction is attributed to Pro. The argument gives a uniform finite bound, including all integer lifts.

**Theorem 1.1 (An explicit lower approximation bound).**

$$\begin{aligned}\forall M,k \in \mathbb{N}, 0<M \Rightarrow 0<k \Rightarrow\\\frac{1}{M(M+3)k} \le |\frac{k\sqrt{2}}{M}-\operatorname{round}(\frac{k\sqrt{2}}{M})|\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/QuadraticRotationHitting.sqrt_two_scaled_round_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be the nearest integer to k sqrt(2)/M. It is nonnegative. Irrationality makes the integer 2k^2-M^2m^2 nonzero, so its absolute value is at least one. Factor this integer as M(k sqrt(2)/M-m)(k sqrt(2)+Mm). The rounding error bounds Mm by k sqrt(2)+M/2; hence k sqrt(2)+Mm<=(M+3)k. Division yields the stated lower bound.

**Theorem 1.2 (A bounded signed mesh with integer lifts).**

$$\begin{aligned}\forall theta,tau,e, e\neq0 \Rightarrow\\\exists j \in N, j|e|<1,\\\exists m \in Z, |theta+je-tau-m|\le|e|\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/QuadraticRotationHitting.signed_rotation_mesh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive step use j=floor(fract(tau-theta)/|e|); for a negative step use floor(fract(theta-tau)/|e|). Floor inequalities give j|e|<1 and a residual of absolute value at most |e|. The signed integer part is kept explicitly, so the estimate includes wrap-around.

**Theorem 1.3 (Uniform hitting from a badly-approximable bound).**

$$\begin{aligned}\forall \alpha,\kappa \in \mathbb{R}, 0<\kappa \Rightarrow\\(\forall k \in \mathbb{N}, 0<k \Rightarrow \frac{\kappa}{k}\le|k\cdot\alpha-\operatorname{round}(k\cdot\alpha)|) \Rightarrow\\\forall p \in \mathbb{N}, 0<p \Rightarrow \forall \theta,a \in \mathbb{R}, 0\le a \Rightarrow a\le\frac{3}{4} \Rightarrow\\\exists j \in \mathbb{N}, j\le\frac{256\cdot p}{\kappa} \land \operatorname{fract}(\theta+j\cdot p\cdot\alpha) \in [a,a+\frac{1}{4}]\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/QuadraticRotationHitting.badly_approximable_quarter_hitting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Natural numbers and rounded integers in real expressions denote their canonical real coercions. Dirichlet at n=16 supplies 1<=q<=16 with beta=|qp alpha-round(qp alpha)|<=1/17. The lower approximation bound gives beta>=kappa/(qp)>0. Aim the signed mesh at a+1/8. Its error beta stays strictly inside the quarter interval, and its integer lift identifies the correct fractional representative. Its original index is jq<=q/beta<=q^2 p/kappa<=256p/kappa. The specialized theorem sqrt_two_scaled_quarter_hitting gives the integral bound 256 M(M+3)p.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/QuadraticRotationHitting.badly_approximable_quarter_hitting`
- Truth anchor: `D5/S1/Dynamics/Shadowing/QuadraticRotationHitting.signed_rotation_mesh`
- Truth anchor: `D5/S1/Dynamics/Shadowing/QuadraticRotationHitting.sqrt_two_scaled_round_lower`
