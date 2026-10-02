# Uniform Divisor Weight Transfer

## Abstract

Factorial congruences preserve relative normalized divisor weights uniformly on exponential height bounds.

**Definition 1.1 (High-prime divisor weight).**

$$\forall m,n\in \mathbb{N}, 0<n\Rightarrow \operatorname{H}\left(m, n\right) = \prod_{p\mid n,\operatorname{Prime}\left(p\right),m<p}\operatorname{z}\left(p, \operatorname{v}\left(p, n\right)\right)\land \forall m\in \mathbb{N}, \operatorname{H}\left(m, 0\right) = 1$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer.highWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive n, H(m,n) is the product of reciprocal geometric sums z(p,v)=sum(i=0..v) p^(-i) over prime divisors p of n greater than m. The exponent v(p,n) is the natural prime factorization exponent. The value H(m,0) is one.

**Definition 1.2 (Complete Euler product).**

$$\forall x\in \mathbb{R}, \operatorname{P}\left(x\right) = \prod_{0<p\le \left\lfloor x\right\rfloor,\operatorname{Prime}\left(p\right)}(1-\frac{1}{p})^{-1}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer.primeProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P(x) is the product of (1-1/p)^(-1) over positive primes p at most the natural floor of the real cutoff x. The natural floor is zero when x is negative.

**Definition 1.3 (Normalized divisor weight).**

$$\forall n\in \mathbb{N}, 0<n\Rightarrow \operatorname{Z}\left(n\right) = \frac{\operatorname{sigma}\left(n\right)}{n}\land \operatorname{Z}\left(0\right) = 0$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer.normalizedWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive natural n, Z(n) is the sum of positive divisors of n divided by n. The value at zero is zero, following real division by zero in the formal definition.

**Definition 1.4 (Uniform relative error).**

$$\forall C\in \mathbb{R}, \forall m\in \mathbb{N}, \operatorname{U}\left(C, m\right) = \operatorname{sup}_{a,b\in \mathbb{N},0<a,0<b,a,b\le \operatorname{exp}\left(Cm\operatorname{log}\left(m\right)\right),a\equiv b\pmod{m!}}\left|\frac{\operatorname{Z}\left(a\right)}{\operatorname{Z}\left(b\right)}-1\right|$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer.uniformError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

U(C,m) is the supremum of the absolute relative errors over positive integers a,b bounded by exp(C*m*log(m)) and congruent modulo m!. The real supremum of an empty admissible set is defined as zero.

**Theorem 1.5 (Cutoff envelope and uniform congruence transfer).**

$$(\forall m,n\in \mathbb{N}, m\ge 2\land 0<n\Rightarrow \forall X\in \mathbb{R}, m\le X\Rightarrow 1\le \operatorname{H}\left(m, n\right)\le\frac{\operatorname{P}\left(X\right)}{\operatorname{P}\left(m\right)}\operatorname{exp}\left(\frac{\operatorname{log}\left(n\right)}{(X-1)\operatorname{log}\left(X\right)}\right))\land (\forall C\in \mathbb{R}, 0<C\Rightarrow \forall epsilon\in \mathbb{R}, 0<epsilon\Rightarrow \exists M\in \mathbb{N}, \forall m\in \mathbb{N}, M\le m\Rightarrow \forall a,b\in \mathbb{N}, 0<a,0<b,a\le \operatorname{exp}\left(Cm\operatorname{log}\left(m\right)\right),b\le \operatorname{exp}\left(Cm\operatorname{log}\left(m\right)\right),a\equiv b\pmod{m!}\Rightarrow \left|\frac{\operatorname{Z}\left(a\right)}{\operatorname{Z}\left(b\right)}-1\right|<epsilon)\land (\forall C\in \mathbb{R}, 0<C\Rightarrow \lim_{m\to\infty}\operatorname{U}\left(C, m\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m >= 2 and positive natural n, every real cutoff X >= m gives the first bound. Write Z(n)=sigma(n)/n, where sigma is the sum of positive divisors. For every fixed positive real C, every positive epsilon admits a natural threshold M. All m >= M and positive a,b bounded by exp(C*m*log(m)) and congruent modulo m! then satisfy the second bound. This is the epsilon form of the third conclusion: U(C,m) tends to zero as m tends to infinity.

Split the actual prime divisors above m at X. Complete the product on m < p <= X to P(X)/P(m). Above X, each logarithmic Euler factor is at most 1/(X-1), and the number of distinct prime divisors is at most log(n)/log(X). The divisor-sum product splits into its small and high prime factors. Set X=m*(log(m))^2. Mertens' product estimate and log(X)/log(m) tending to one make the complete interval product tend to one. The height bound makes the remaining exponential factor tend to one uniformly. The factorial congruence squeeze controls the small factors; applying the same bounds to a and b in both orders gives the absolute relative error bound.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer.highWeight`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer.normalizedWeight`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer.primeProduct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer.uniformError`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer](ModularDivisorWeightTransfer.md)
