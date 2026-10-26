# Positive JJ reciprocal interpolation exclusion

## Abstract

Positive Fibonacci reciprocal data cannot interpolate across the original JJ clocks.

Let m and a be nonnegative integers, with m at least five and a at most K=2m-2. Let r be a positive real number and let u be the actual sequence with u(0)=1, u(1)=-r and u(k+2)=u(k+1)+u(k). The prefix evaluates a polynomial at clocks 0 through a, while the suffix evaluates it at clocks a+2 through K+2. The exponent a therefore supplies two equations, at the distinct clocks a and a+2.

**Theorem 1.1 (Full original-clock interpolation obstruction).**

$$\forall m \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall r \in \mathbb{R},\; \forall u \in \mathbb{N} \to \mathbb{R},\; \left(5 \le m \land \left(a \le 2 \cdot m - 2 \land \left(0 < r \land \left(u\left(0\right) = 1 \land \left(u\left(1\right) = -r \land \left(\forall k \in \mathbb{N},\; u\left(k + 2\right) = u\left(k + 1\right) + u\left(k\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\neg \left(\exists R \in \operatorname{Polynomial}\left(\mathbb{R}\right),\; \operatorname{natDegree}\left(R\right) \le m - 1 \land \left(\left(\forall k \in \mathbb{N},\; k \le 2 \cdot m - 2 \Rightarrow u\left(k\right) \ne 0\right) \land \left(\left(\forall k \in \mathbb{N},\; k \le a \Rightarrow u\left(k\right) \cdot \operatorname{eval}\left(R, k\right) = 1\right) \land \left(\forall k \in \mathbb{N},\; a \le k \Rightarrow \left(k \le 2 \cdot m - 2 \Rightarrow u\left(k\right) \cdot \operatorname{eval}\left(R, k + 2\right) = 1\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Interpolation/PositiveJJExclusion.positive_jj_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The degree bound includes constants and every lower actual degree. Since the prefix contains clock zero, any candidate has R(0)=1 and is nonzero. For nonzero real polynomials, natDegree is the ordinary degree. Natural m and a represent exactly the integer ranges in the statement. Every sampled denominator through K is required to be nonzero; no further parameter, parity, root or determinant premise is imposed.

The Fibonacci solution-space decomposition gives u(k)=A phi^k+B psi^k, where phi is the positive golden ratio, psi its negative conjugate, and B>0. Let s be the left index of the first same-sign pair before K, or set s=K if there is no such pair. Before s, adjacent values have opposite signs. A same-sign pair gives A u(s)>0 through u(s+1)-psi u(s)=A phi^s(phi-psi); the recurrence then gives A u(k)>0 for every k at least s. Thus A is nonzero whenever this tail is used.

Put H(t)=exp(log(phi)t)R(t) and Q=R'+log(phi)R. Then H'(t)=exp(log(phi)t)Q(t). The coefficient of Q at the actual degree of R is log(phi) times the nonzero leading coefficient of R. Consequently Q is nonzero and its degree is at most that of R, including the constant case. On a block shifted by h=0 or h=2, the interpolation equations give (A u(k))(H(k+h)-phi^h/A)=-phi^h B psi^k. Its consecutive residuals have opposite signs on the same-sign tail. Before the transition, the values of H themselves have opposite signs.

If s is at most a, use the open intervals (0,s), (s,a) and (a+2,K+2), with edge counts s, a-s and K-a. If a is less than s, use (0,a), (a+2,s+2) and (s+2,K+2), with counts a, s-a and K-s. These intervals are disjoint in either case, and the counts sum to K. An alternating block with n edges gives n distinct level crossings by the intermediate value theorem; Rolle interleaving gives n at most one plus the number of roots of Q in that interval. This inequality also holds for an empty block. Summing gives K at most deg(Q)+3, and hence 2m-2 at most m+2, contradicting m at least five.

The two shifted levels are differentiated separately; no crossing across the omitted-clock gap is counted. Both transition parities and the case with no same-sign pair are included. The exponential is an auxiliary function in the proof and adds no acquisition or observation.

Excluding interpolation excludes any criterion that requires these same equations together with a separate determinant condition. It determines no determinant value, sign or singularity. The fixed-word gain-ray application additionally uses the critical mixed-word classification: its acquisition word and countable matrix palette are preassigned, and different words or palettes may have different failure worlds. No adaptive, common-world, complete-target, calibration or physical resource conclusion is supplied by the auxiliary weight.

## References

- Truth anchor: `D5/S1/Recurrence/Interpolation/PositiveJJExclusion.positive_jj_exclusion`
- Dependency: [D5/S1/Recurrence/BilateralLiftUniqueness](../BilateralLiftUniqueness.md)
