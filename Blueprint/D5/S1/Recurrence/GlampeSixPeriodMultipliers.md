# Polynomial Multipliers of a Scaled Six-Period Recurrence

## Abstract

A scaled six-period recurrence has literal sign-restricted identities exactly for multipliers congruent to one modulo six.

Equation (10) of Glampe, Joshi, Malla, Richey and Wright, arXiv:2610.15131v1, asks which multipliers admit a polynomial identity with an optional index-dependent sign on each coefficient.

**Definition 1.1 (The scaled sequence).**

$$\forall t \in \mathbb{Z}, G_{0}=1, G_{1}=0, \forall n \in \mathbb{N}, G_{n+2}=tG_{n+1}-t^{2}G_{n}$$

*Formalization.* `D5/S1/Recurrence/GlampeSixPeriodMultipliers.scaledGibonacci` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every integer scale t, the integer sequence G has seeds 1 and 0. The solution of the order-two recurrence is G(n)=t^n h(n), where h repeats (1,0,-1,-1,0,1). The table has the same seeds and satisfies h(n+2)=h(n+1)-h(n), which gives the formula by recurrence uniqueness.

**Theorem 1.2 (Classification with a fixed sign bit per degree).**

$$\forall t\in\mathbb{Z}, \forall k\in\mathbb{N}, \left(2 \leq \lvert t\rvert \land k>0\right) \Rightarrow \left(\left(\exists c \in K^{k+1}, \exists \varepsilon: \operatorname{Fin}\left(k+1\right) \to \{0,1\}, \forall n\in\mathbb{N}, G_{kn}=\sum_{i=0}^{k} c_{i}\left(-1\right)^{n\varepsilon_{i}}G_{n}^{i}\right) \iff k\equiv1\pmod{6}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GlampeSixPeriodMultipliers.multipliers_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any characteristic-zero field K, an integer t with absolute value at least two, and a positive natural multiplier k. Each G value in the identity is cast from the integers into K. The coefficients and bits are fixed for all natural indices, including zero, and the bound k includes every smaller degree.

At indices 1 and 7, the inputs are both zero and the two signs agree for each bit. The outputs must therefore agree. Since h(7k)=h(k) and the powers of t have distinct values at distinct exponents, h(k)=0. Only residues 1 and 4 modulo six give that value.

Every sign factor is one at an even index. At indices 6j, the resulting even-index polynomial agrees with X^k at the infinitely many distinct points t^(6j), so it equals X^k. If k is congruent to four, then G(2k)=-t^(2k) while G(2)^k=t^(2k). The scale bound and characteristic zero make those values distinct.

If k is congruent to one, then h(kn)=h(n) and k is odd. Each entry of the period is fixed by raising it to the kth power, so G(kn)=G(n)^k. Take the coefficient of degree k to be one, every other coefficient to be zero, and every sign bit to be zero.

## References

- Truth anchor: `D5/S1/Recurrence/GlampeSixPeriodMultipliers.multipliers_iff`
- Truth anchor: `D5/S1/Recurrence/GlampeSixPeriodMultipliers.scaledGibonacci`
