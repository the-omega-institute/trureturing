# Polynomial Multipliers of a Scaled Six-Period Recurrence

## Abstract

For integer scales of absolute value at least two, a scaled six-period recurrence admits fixed-sign polynomial identities over any characteristic-zero field exactly for positive multipliers congruent to one modulo six.

The source's equation (10) asks which multipliers admit a polynomial identity with an optional parity sign on each coefficient. The family considered here has G(0)=1, G(1)=0 and (r,s)=(t,-t²) in equation (9). The general classification for equation (9) remains open in this development.

**Definition 1.1 (The scaled sequence).**

$$\forall t \in \mathbb{Z}, G_{t,0}=1, G_{t,1}=0, \forall n \in \mathbb{N}, G_{t,n+2}=tG_{t,n+1}-t^{2}G_{t,n}$$

*Formalization.* `D5/S1/Recurrence/GlampeSixPeriodMultipliers.scaledGibonacci` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joey Glampe, Aryaman Joshi, Swagat Malla, Matthew Richey, Matthew Wright (2026). *Polynomial Identities for Generalized Fibonacci Sequences*. URL: <https://arxiv.org/abs/2610.15131v1>.

*Commentary.*

For every integer scale t, write G(t,n) for scaledGibonacci t n, the integer sequence with seeds 1 and 0. The solution of the order-two recurrence is G(n)=t^n h(n), where h repeats (1,0,-1,-1,0,1). The table has the same seeds and satisfies h(n+2)=h(n+1)-h(n), which gives the formula by recurrence uniqueness.

**Theorem 1.2 (Classification with a fixed sign bit per degree).**

$$\forall K: Type*, [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)], \forall t\in\mathbb{Z}, \forall k\in\mathbb{N}, \left(2 \leq \lvert t\rvert \land k>0\right) \Rightarrow \left(\left(\exists c: \operatorname{Fin}\left(k+1\right) \to K, \exists \varepsilon: \operatorname{Fin}\left(k+1\right) \to \{0,1\}, \forall n\in\mathbb{N}, \operatorname{IntCast}_{K}\left(G_{t,kn}\right)=\sum_{i=0}^{k} c_{i}\left(-1: K\right)^{n\varepsilon_{i}}\operatorname{IntCast}_{K}\left(G_{t,n}\right)^{i}\right) \iff k\equiv1\pmod{6}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GlampeSixPeriodMultipliers.multipliers_iff` (`✓ std3`). ∎

*Resolves.* `Problems/glampe-2026-six-period-multipliers` (proved) by `D5/S1/Recurrence/GlampeSixPeriodMultipliers.multipliers_iff`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"glampe-2026-six-period-multipliers","declaration_gid":"D5/S1/Recurrence/GlampeSixPeriodMultipliers.multipliers_iff","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joey Glampe, Aryaman Joshi, Swagat Malla, Matthew Richey, Matthew Wright (2026). *Polynomial Identities for Generalized Fibonacci Sequences*. URL: <https://arxiv.org/abs/2610.15131v1>.

*Commentary.*

Fix any characteristic-zero field K, an integer t with absolute value at least two, and a positive natural multiplier k. IntCast_K is the canonical integer-to-K cast, and the sign base -1 is an element of K. Each bit is zero for the false Boolean mask value and one for true. The coefficients and bits are fixed for all natural indices, including zero, and the bound k includes every smaller degree.

At indices 1 and 7, the inputs are both zero and the two signs agree for each bit. The outputs must therefore agree. Since h(7k)=h(k) and the powers of t have distinct values at distinct exponents, h(k)=0. Only residues 1 and 4 modulo six give that value.

Every sign factor is one at an even index. At indices 6j, the resulting even-index polynomial agrees with X^k at the infinitely many distinct points t^(6j), so it equals X^k. If k is congruent to four, then G(2k)=-t^(2k) while G(2)^k=t^(2k). The scale bound and characteristic zero make those values distinct.

If k is congruent to one, then h(kn)=h(n) and k is odd. Each entry of the period is fixed by raising it to the kth power, so G(kn)=G(n)^k. Take the coefficient of degree k to be one, every other coefficient to be zero, and every sign bit to be zero.

## References

- Truth anchor: `D5/S1/Recurrence/GlampeSixPeriodMultipliers.multipliers_iff`
- Truth anchor: `D5/S1/Recurrence/GlampeSixPeriodMultipliers.scaledGibonacci`
