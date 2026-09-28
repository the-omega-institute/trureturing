# Equivariant Series Observer

## Abstract

Power closure characterizes recovery of unrestricted bivariate class-function series.

**Theorem 1.1 (Recovery and conjugacy-saturated power closure).**

$$\begin{aligned}\operatorname{Sat}\left(S\right) = \{g \mid \exists s \in S, s \sim g\},\\\operatorname{Rec}\left(S\right) := \forall H_{1}, H_{2} \in C_{G}, (\operatorname{Phi}\left(H_{1}\right)|_{S} = \operatorname{Phi}\left(H_{2}\right)|_{S}) \Rightarrow H_{1}|_{S} = H_{2}|_{S},\\\operatorname{Rec}\left(S\right) \Leftrightarrow \forall g \in \operatorname{Sat}\left(S\right), \forall n \in \mathbb{N}, 0 < n \Rightarrow g^{n} \in \operatorname{Sat}\left(S\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/EquivariantSeriesObserver.observed_recovery_iff_power_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be any group, S any subset of G, and K any characteristic-zero field, including the rationals. A family H assigns to each group element a formal bivariate series over K. The domain C consists of every such family whose coefficients vanish when either exponent is zero and whose values agree on conjugate elements. Coefficients may have either sign; no finite-group, convergence, or representation hypothesis is imposed.

For positive m and n, the coefficient of p^m q^n in the logarithmic history of H at g is the finite sum, over k dividing gcd(m,n), of H at g^k and exponent pair (m/k,n/k), divided by k. Coefficients with a zero exponent vanish. Recovery on S means that equality of these histories on S implies equality of the original families on S for every pair in C.

Conjugacy saturation contains exactly the elements conjugate to some element of S. The equivalence says that recovery holds precisely when this saturation contains every positive power of each of its elements. For sufficiency, the divisor-one term gives the coefficient at g; all other terms use smaller exponents at powers of g still in the saturation, so induction recovers each coefficient. For necessity, a Mobius-inverted class-function series has logarithmic history concentrated on a missing conjugacy class. If s is observed and s^r lies in that class for a prime r, its original coefficient at s in degree (r,r) is -1/r, so recovery fails. It applies to the unrestricted domain C; actual representation traces and VOA traces form narrower domains for which necessity is not asserted.

## References

- Truth anchor: `D5/S3/Analytic/Dilation/EquivariantSeriesObserver.observed_recovery_iff_power_closed`
