# Binet Tails and Positive Response

## Abstract

The infinite logarithmic Binet tails give a strictly positive Dirichlet response.

**Definition 1.1 (The literal Binet coefficient).**

$$\forall q\in \mathbb{R}, \forall n\in \mathbb{N}, \operatorname{b}\left(q, n\right)= \operatorname{log}\left(1-(-q)^{n}\right), \operatorname{b}\left(q, 0\right)=0$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real q and natural n, b(q,n) is log(1-(-q)^n), bundled as a real arithmetic function. In Lean log(0)=0, so b(q,0)=0. At the actual Fibonacci parameter q=phi^(-2), this is the logarithmic Binet correction. The definition makes no sign or convergence assertion for arbitrary q.

**Definition 1.2 (The complete negative tail).**

$$\forall q\in \mathbb{R}, \operatorname{E}\left(q\right)= \sum_{j\in \mathbb{N}}-\operatorname{b}\left(q, 2(j+1)\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse.negativeTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E(q) is the infinite sum of -b(q,2(j+1)) over all natural j. For 0<q<=2/5 these are precisely the negative coefficient magnitudes, starting at index two. Convergence is proved in the contract below, not assumed in this total definition using Lean's tsum.

**Definition 1.3 (The complete positive tail after the head).**

$$\forall q\in \mathbb{R}, \operatorname{P}\left(q\right)= \sum_{j\in \mathbb{N}}\operatorname{b}\left(q, 2(j+1)+1\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse.positiveTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P(q) is the infinite sum of b(q,2(j+1)+1) over all natural j. For 0<q<=2/5 these are precisely the positive coefficients after b(q,1), starting at index three. The head is excluded from both tails.

**Definition 1.4 (The response to the arithmetic logarithm).**

$$\forall q\in \mathbb{R}, 0< q\Rightarrow \operatorname{k}\left(q\right)= \operatorname{b}\left(q\right)^{-1}*\log$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse.response` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each q>0, k(q) is the existing arithmetic-function Dirichlet inverse of b(q), multiplied by the existing arithmetic logarithm. The product and inverse in this display are Dirichlet convolution operations. Since b(q,1)=log(1+q)>0, the head is invertible. The value at zero is zero by the bundled arithmetic-function convention; the proof of q>0 has no mathematical effect on the response.

**Theorem 1.5 (Summable tails, a quantitative gap, and a positive response).**

$$\forall q\in \mathbb{R}, 0< q\le \frac{2}{5}\Rightarrow (\operatorname{Summable}\left(j\mapsto-\operatorname{b}\left(q, 2(j+1)\right)\right)\land \operatorname{Summable}\left(j\mapsto\operatorname{b}\left(q, 2(j+1)+1\right)\right)\land \frac{94\cdot q}{2205}\le \operatorname{b}\left(q, 1\right)-\operatorname{E}\left(q\right)-\operatorname{P}\left(q\right)\land (\forall n\in \mathbb{N}, (\sum_{d\in \operatorname{D}\left(n\right), d\neq1}\operatorname{max}\left(-\operatorname{b}\left(q, d\right), 0\right)\le \operatorname{E}\left(q\right)\land \sum_{d\in \operatorname{D}\left(n\right), d\neq1}\operatorname{max}\left(\operatorname{b}\left(q, d\right), 0\right)\le \operatorname{P}\left(q\right)))\land \operatorname{k}\left(q, 1\right)=0\land (\forall n\in \mathbb{N}, 0< n\Rightarrow \frac{\operatorname{b}\left(q, 1\right)-\operatorname{E}\left(q\right)-\operatorname{P}\left(q\right)}{\operatorname{b}\left(q, 1\right)\cdot(\operatorname{b}\left(q, 1\right)-\operatorname{E}\left(q\right))}\cdot\operatorname{log}\left(n\right)\le \operatorname{k}\left(q, n\right)\le \frac{\operatorname{log}\left(n\right)}{\operatorname{b}\left(q, 1\right)-\operatorname{E}\left(q\right)})\land (\forall n\in \mathbb{N}, 1< n\Rightarrow 0< \operatorname{k}\left(q, n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse.binet_response_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real q with 0<q<=2/5, both infinite tail sequences are summable, and b(q,1)-E(q)-P(q)>=94q/2205. For every natural n, the sum of max(-b(q,d),0) over D(n) excluding 1 is at most E(q), and the sum of max(b(q,d),0) over the same set is at most P(q). Here D(n) is the finite positive-divisor set, with D(0) empty. The response satisfies k(q,1)=0; at every n>0 it is between (b(q,1)-E(q)-P(q))log(n)/(b(q,1)(b(q,1)-E(q))) and log(n)/(b(q,1)-E(q)); at every n>1 it is strictly positive.

Parity identifies the even negative terms and odd positive terms. With r=q^2, the negative term at 2(j+1) is bounded by q^2 r^j/(1-q^2), and the positive term at 2(j+1)+1 is bounded by q^3 r^j. Geometric summability gives E(q)<=q^2/(1-q^2)^2 and P(q)<=q^3/(1-q^2). Splitting the shifted max sequences into their even and odd subsequences identifies their complete sums with E and P. The injective shift d to d-2 transfers these nonnegative infinite budgets to every finite divisor set excluding the head.

The logarithmic head satisfies b(q,1)>=4q/5. The two geometric estimates give E(q)<=250q/441 and P(q)<=4q/21, leaving the stated gap. The upstream inverse identity discharges b(q)*k(q)=log exactly. The previously proved signed divisor response comparison then supplies both bounds, and their positive lower coefficient gives strict positivity when n>1. The conclusion retains the true infinite E and P, rather than substituting their geometric majorants.

This is an infinite analytic parameter family. It closes the Binet budget premises of the positive response mechanism. It supplies no atom/lcm reconstruction identity, critical-scale cancellation estimate, signed Robin tail bound, or proof of RH.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse.beta`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse.binet_response_contract`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse.negativeTail`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse.positiveTail`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse.response`
- Dependency: [D5/S3/Arith/SignedDirichletPositiveResponse](../SignedDirichletPositiveResponse.md)
