# Long division, infinite positional values, and period quotients

## Abstract

Integer long division realizes rational values and prescribed periods.

**Definition 1.1 (Recursive remainder).**

$$\forall b\in \mathbb{N}, \forall p\in \mathbb{N}, \forall q\in \mathbb{N}, \operatorname{remainder}(b, p, q, 0)= p\land \forall n\in \mathbb{N}, \operatorname{remainder}(b, p, q, n+ 1)= \operatorname{mod}(b\operatorname{remainder}(b, p, q, n), q)$$

*Formalization.* `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.remainder` (`✓ std3`).

*Citation.* Eric W. Weisstein (2026). *Repeating Decimal*. URL: <https://mathworld.wolfram.com/RepeatingDecimal.html>.

*Commentary.*

For natural b, p, q, start with r(0)=p and repeatedly multiply by b and take the remainder modulo q. The definition is total, including q=0.

**Definition 1.2 (Quotient digit).**

$$\forall b\in \mathbb{N}, \forall p\in \mathbb{N}, \forall q\in \mathbb{N}, \forall n\in \mathbb{N}, \operatorname{digit}(b, p, q, n)= \operatorname{div}(b\operatorname{remainder}(b, p, q, n), q)$$

*Formalization.* `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.digit` (`✓ std3`).

*Citation.* Eric W. Weisstein (2026). *Repeating Decimal*. URL: <https://mathworld.wolfram.com/RepeatingDecimal.html>.

*Commentary.*

The operator div is natural-number division: the digit at position n is the quotient of b times the current remainder by q. Under b>1 and p<q, every remainder is less than q and every digit is less than b. The latter bound supplies Mathlib's finite digit alphabet in the summability proof.

**Definition 1.3 (Positional integer prefix).**

$$\forall b\in \mathbb{N}, \forall p\in \mathbb{N}, \forall q\in \mathbb{N}, \operatorname{longDivisionPrefix}(b, p, q, 0)= 0\land \forall n\in \mathbb{N}, \operatorname{longDivisionPrefix}(b, p, q, n+ 1)= b\operatorname{longDivisionPrefix}(b, p, q, n)+ \operatorname{digit}(b, p, q, n)$$

*Formalization.* `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.longDivisionPrefix` (`✓ std3`).

*Citation.* Eric W. Weisstein (2026). *Repeating Decimal*. URL: <https://mathworld.wolfram.com/RepeatingDecimal.html>.

*Commentary.*

P(0)=0 and P(n+1)=b P(n)+d(n). Thus the first generated digit is the most significant digit of the n-digit integer prefix; leading zeroes are allowed.

**Theorem 1.4 (Conserved scaled numerator).**

$$\forall b\in \mathbb{N}, \forall p\in \mathbb{N}, \forall q\in \mathbb{N}, \forall n\in \mathbb{N}, q\operatorname{longDivisionPrefix}(b, p, q, n)+ \operatorname{remainder}(b, p, q, n)= b^{n}p$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.long_division_invariant` (`✓ std3`). ∎

*Citation.* Eric W. Weisstein (2026). *Repeating Decimal*. URL: <https://mathworld.wolfram.com/RepeatingDecimal.html>.

*Commentary.*

For every natural b,p,q,n, including zero base or denominator, the recursive state satisfies q P(n)+r(n)=b^n p. The proof inducts on n and uses the Euclidean division identity at each step. Neither the prefix nor the remainder is defined by the claimed closed form.

**Theorem 1.5 (The infinite positional value).**

$$\forall b\in \mathbb{N}, \forall p\in \mathbb{N}, \forall q\in \mathbb{N}, 1< b\land p< q\Rightarrow \operatorname{HasSum}((\operatorname{fun} n: \mathbb{N}\mapsto \frac{(\operatorname{digit}(b, p, q, n): \mathbb{R})}{(b: \mathbb{R})^{n+ 1}}), \frac{(p: \mathbb{R})}{(q: \mathbb{R})})\land \operatorname{Tendsto}((\operatorname{fun} n: \mathbb{N}\mapsto \frac{(\operatorname{longDivisionPrefix}(b, p, q, n): \mathbb{R})}{(b: \mathbb{R})^{n}}), \operatorname{atTop}, \operatorname{nhds}(\frac{(p: \mathbb{R})}{(q: \mathbb{R})}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.long_division_value` (`✓ std3`). ∎

*Citation.* Eric W. Weisstein (2026). *Repeating Decimal*. URL: <https://mathworld.wolfram.com/RepeatingDecimal.html>.

*Commentary.*

For every natural base b>1 and p<q, the digit series has sum p/q in the reals, and P(n)/b^n tends to p/q as n tends to infinity. Natural p<q implies q>0. The prefix-to-partial-sum induction and conserved numerator express the error as r(n)/(q b^n), bounded by b^(-n). Mathlib supplies geometric convergence and summability of finite-alphabet positional digits. This proves infinite-series semantics for the actual recursively generated digits.

**Theorem 1.6 (Prescribed period and block quotient).**

$$\forall b\in \mathbb{N}, \forall p\in \mathbb{N}, \forall q\in \mathbb{N}, 1< b\land p< q\Rightarrow \forall L\in \mathbb{N}, q\mid (b^{L}- 1)\Rightarrow (\forall n\in \mathbb{N}, \operatorname{digit}(b, p, q, n+ L)= \operatorname{digit}(b, p, q, n))\land ((b: \mathbb{R})^{L}- 1)\frac{(p: \mathbb{R})}{(q: \mathbb{R})}= (\operatorname{longDivisionPrefix}(b, p, q, L): \mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.long_division_period` (`✓ std3`). ∎

*Citation.* Eric W. Weisstein (2026). *Repeating Decimal*. URL: <https://mathworld.wolfram.com/RepeatingDecimal.html>.

*Commentary.*

For b>1, p<q and any natural L with q dividing b^L-1, the digit at n+L equals the digit at n for every natural n, and (b^L-1)(p/q)=P(L) over the reals. The invariant first gives r(L)=p; induction propagates this return through the actual remainder recurrence. L=0 gives the trivial period and zero shift. For L>0 the positive shift factor gives p/q=P(L)/(b^L-1). The period need not be minimal, and no converse classification is asserted.

Chapter 36's repeating-decimal example uses b=10, p=1, q=7, L=6. Long division generates 1,4,2,8,5,7, with P(6)=142857; 7 divides 10^6-1. Periodicity and the first six digits identify the infinite stream as 0.overline{142857}; its convergent series is 1/7. The block identity is 10^6 x-x=142857, hence x=142857/999999=1/7. These values specialize the general long-division theorems.

These are classical long-division and repeating-decimal facts. The cited MathWorld entry attests the classical context; the arbitrary-base integer-state-to-real-series connection is the formal bridge proved here. No novelty claim or statement about the chapter's philosophical parable follows.

## References

- Truth anchor: `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.digit`
- Truth anchor: `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.longDivisionPrefix`
- Truth anchor: `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.long_division_invariant`
- Truth anchor: `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.long_division_period`
- Truth anchor: `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.long_division_value`
- Truth anchor: `D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.remainder`
