# A Half-Exponential Rate for Weighted Fibonacci Rows

## Abstract

Weighted Fibonacci fractional-part sums and their reciprocal-floor rows have a common half-exponential error bound.

Let F be the standard Fibonacci sequence, with F(0)=0 and F(1)=1. Let phi=(1+sqrt(5))/2. The function fract is the real fractional part x-floor(x), and floor takes integer values.

**Definition 1.1 (Weighted fractional-part sum).**

$$\operatorname{W}\left(n\right) = \sum_{1 \le k \le n}\operatorname{F}\left(k\right)\cdot \operatorname{fract}\left(\frac{\operatorname{F}\left(n\right)}{\operatorname{F}\left(k\right)}\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WeightedInghamRate.weightedSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum runs over all positive indices k at most n. Each summand is also the integer remainder of F(n) on division by F(k). The empty sum at n=0 is zero.

**Definition 1.2 (Reciprocal-floor kernel).**

$$\operatorname{Phi}\left(x\right) = x\cdot \left\lfloor\frac{1}{x}\right\rfloor$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WeightedInghamRate.inghamKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive x the kernel multiplies x by the integer part of its reciprocal. At x=0 real field division gives zero.

**Theorem 1.3 (A common error bound).**

$$\begin{aligned}\exists C > 0, \exists N0\in\mathbb{N}, \forall n\in\mathbb{N}, N0 \le n \Rightarrow\\\Vert\frac{\operatorname{W}\left(n\right)}{\operatorname{F}\left(n\right)}-\frac{2}{\sqrt{5}}\Vert \le C\cdot phi^{\frac{-n}{2}} \land\\\Vert\sum_{1 \le k \le n}\operatorname{Phi}\left(\frac{\operatorname{F}\left(k\right)}{\operatorname{F}\left(n\right)}\right)-(n-\frac{2}{\sqrt{5}})\Vert \le C\cdot phi^{\frac{-n}{2}}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/WeightedInghamRate.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are a positive real C and a natural threshold N0 such that both inequalities hold for every natural n>=N0, with the same C and N0. The exponent is the real number -n/2. One choice is C=4096 and N0=16.

Put j=n-k. In the main segment 1<=j and 2j+3<=n, the integer Fibonacci addition identity determines the weighted fractional part exactly: it is F(n-j)-F(n-2j) for even j, and F(n-2j) for odd j. The strict inequalities 0<F(n-2j)<F(n-j) fix the integer quotient.

Pairing j=2t+1 with j=2t+2 gives F(n-2t-2)+F(n-4t-3). For m=floor((n-4)/4), this finite paired sum telescopes to (4F(n+1)-2F(n))/5 plus boundary terms. The remaining terms are nonnegative and their sum is bounded by the sum of their Fibonacci weights.

Fibonacci power bounds control all boundary terms by a constant times phi to the power n/2. Dividing by F(n), and using the exact golden residual of consecutive Fibonacci numbers, gives the first inequality. For each positive Fibonacci ratio, Phi(F(k)/F(n)) equals 1-(F(k)/F(n))*fract(F(n)/F(k)); summing this equality gives the second inequality.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WeightedInghamRate.inghamKernel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WeightedInghamRate.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WeightedInghamRate.weightedSum`
- Dependency: [D5/S3/Axis/AxisConvergence](../../Axis/AxisConvergence.md)
