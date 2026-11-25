# Bounds between active prime powers

## Abstract

A finite test for the character ramp on an entire real interval

Let χ be a nonprincipal complex character of positive modulus. Write D for L′(1,χ)/L(1,χ). Then g(x) is xD plus the sum of Λ(n)χ(n) max(x/n − 1,0) over positive integers n ≤ x. Given Y ≤ Z, let S consist of Y, Z and the positive integers strictly between them for which Λ(n)χ(n) is nonzero. All such integers are prime powers coprime to the modulus.

**Theorem 1.1 (Comparison with any concave function on the window).**

$$\left(\forall x \in I,\; \operatorname{abs}\left(\operatorname{g}\left(x\right)\right) \le \operatorname{B}\left(x\right)\right) \Leftrightarrow \left(\forall t \in S,\; \operatorname{abs}\left(\operatorname{g}\left(t\right)\right) \le \operatorname{B}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletRampWindow.concave_window_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here I is the real interval [Y,Z] and B is concave on I. The endpoints can be negative or equal. For every real x in the interval, take the closest members of S below and above x. The finite sum for g can use the same cutoff throughout that segment. Each positive-part term is affine there, vanishes there, or has zero coefficient. Thus g interpolates its two bounding values. Convexity of the complex norm and concavity of B give the bound at x.

**Theorem 1.2 (One logarithmic derivative test and a finite power-envelope test).**

$$\left(\forall x \in I,\; \operatorname{abs}\left(\operatorname{g}\left(x\right)\right) \le \operatorname{P}\left(x\right) \land \operatorname{abs}\left(D\right) \le c \operatorname{log}\left(x\right)\right) \Leftrightarrow \left(\left(\forall t \in S,\; \operatorname{abs}\left(\operatorname{g}\left(t\right)\right) \le \operatorname{P}\left(t\right)\right) \land \operatorname{abs}\left(D\right) \le c \operatorname{log}\left(Y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletRampWindow.power_log_window_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here 0 < Y ≤ Z, P(x) = A xᵖ, 0 ≤ p ≤ 1, and A,c ≥ 0. The function P is concave on this interval. The derivative D uses the same χ and is independent of x, while c log x increases weakly. Consequently its single test at Y suffices. The choices A = 1 and c = 4 give the paired estimates used for a character host.

## References

- Truth anchor: `D5/S3/CharacterSums/DirichletRampWindow.concave_window_iff`
- Truth anchor: `D5/S3/CharacterSums/DirichletRampWindow.power_log_window_iff`
- Dependency: [D5/S3/CharacterSums/DirichletRampEndpoint](DirichletRampEndpoint.md)
