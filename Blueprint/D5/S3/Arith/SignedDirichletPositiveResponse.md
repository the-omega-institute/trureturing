# Positive Response for Signed Divisor Convolution

## Abstract

Separate positive and negative divisor budgets control a signed response.

**Theorem 1.1 (Two bounds from monotone nonnegative forcing).**

$$\forall b,f,g: \mathbb{N}\to \mathbb{R}, \forall E,P\in \mathbb{R}, ((\forall n\in \mathbb{N}, 0< n\Rightarrow 0\le \operatorname{g}\left(n\right))\land (\forall m,n\in \mathbb{N}, 0< m\le n\Rightarrow \operatorname{g}\left(m\right)\le \operatorname{g}\left(n\right))\land (\forall n\in \mathbb{N}, \sum_{d\in \operatorname{D}\left(n\right), d\neq 1}\operatorname{max}\left(-\operatorname{b}\left(d\right), 0\right)\le E)\land (\forall n\in \mathbb{N}, \sum_{d\in \operatorname{D}\left(n\right), d\neq 1}\operatorname{max}\left(\operatorname{b}\left(d\right), 0\right)\le P)\land E+P< \operatorname{b}\left(1\right)\land (\forall n\in \mathbb{N}, 0< n\Rightarrow \sum_{d\in \operatorname{D}\left(n\right)}\operatorname{b}\left(d\right)\cdot\operatorname{f}\left(\frac{n}{d}\right)= \operatorname{g}\left(n\right)))\Rightarrow \forall n\in \mathbb{N}, 0< n\Rightarrow \frac{\operatorname{b}\left(1\right)-E-P}{\operatorname{b}\left(1\right)\cdot(\operatorname{b}\left(1\right)-E)}\cdot\operatorname{g}\left(n\right)\le \operatorname{f}\left(n\right)\le \frac{\operatorname{g}\left(n\right)}{\operatorname{b}\left(1\right)-E}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SignedDirichletPositiveResponse.signedDivisor_positive_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let b, f and g be real sequences on the natural numbers. Assume g(n)>=0 for every n>0 and g(m)<=g(n) whenever 0<m<=n. Write D(n) for the finite set of positive divisors of n, with D(0) defined to be empty. For every natural n, assume the sums of max(-b(d),0) and max(b(d),0) over divisors d of n other than 1 are at most E and P, respectively. Assume E+P<b(1). At every positive n the exact divisor convolution sum b(d) f(n/d) equals g(n). Then f(n) lies between (b(1)-E-P)g(n)/(b(1)(b(1)-E)) and g(n)/(b(1)-E). Division inside f is natural division and is exact at each divisor.

The empty tails at n=1 imply E>=0 and P>=0, so both denominators and the lower coefficient are positive. Strong induction proves both bounds together. For every divisor d>1, the earlier response satisfies 0<=f(n/d)<=g(n)/(b(1)-E). Consequently the signed tail is at least -E g(n)/(b(1)-E) and at most P g(n)/(b(1)-E). Splitting the head from the convolution and cancelling b(1)>0 gives the upper and lower bounds. Earlier positivity is derived from the inductive lower bound, rather than assumed.

This result allows both positive and negative tail coefficients, zero forcing and arbitrary values of b, f and g at zero. It assumes no global bound or positivity of f. It is a general divisor convolution estimate. Applying it to the actual Fibonacci logarithmic coefficients still requires their budgets and exact convolution identity; those analytic premises are not formalized here. It supplies neither an RH growth estimate nor control of the signed Robin tail.

## References

- Truth anchor: `D5/S3/Arith/SignedDirichletPositiveResponse.signedDivisor_positive_response`
