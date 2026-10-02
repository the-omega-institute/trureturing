# Euler Valuation Moment Comparison

## Abstract

An explicit logarithmic comparison of full valuation and prime-support Euler moments.

For a prime p and a natural exponent a, Z_p(a) is the sum of p^(-j) for 0 <= j <= a. Define U_p(s) as (1-1/p) times the sum over a >= 0 of Z_p(a)^s p^(-a), and define W_p(s) as 1-1/p+(1/p)(1-1/p)^(-s). Real powers are used. U(s) and W(s) are the products of these local factors over every prime.

**Theorem 1.1 (Convergence and logarithmic comparison).**

$$\begin{aligned}\forall s \in \mathbb{R}, 4 \le s \Rightarrow\\\forall p prime, Summable\left(a \mapsto Z_{p}\left(a\right)^{s} p^{-a}\right), 1 \le U_{p}\left(s\right) \le W_{p}\left(s\right)\\Multipliable\left(p \mapsto U_{p}\left(s\right)\right), Multipliable\left(p \mapsto W_{p}\left(s\right)\right)\\0 < U\left(s\right), 0 < W\left(s\right)\\0 \le \log\left(W\left(s\right)\right)-\log\left(U\left(s\right)\right) \le \sqrt{s}(\log\left(s\right)+5)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/EulerValuationMomentComparison.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real moment order s is at least four. Every local valuation series converges, the local factors lie between one and W_p(s), and both full prime products converge to strictly positive real numbers. Multipliable denotes convergence of the net of finite products.

A single term near the critical exponent log(s)/log(p) controls the logarithmic loss for p <= sqrt(s). For larger primes the local loss is at most s/(p squared minus one), and the integer tail telescopes. Combining the two ranges gives the displayed bound.

The definition and large-moment asymptotic of W(s) are given in Andreas Weingartner, The distribution functions of sigma(n)/n and n/phi(n), II, arXiv:1011.4262v1, equation (5) and Lemma 5. The explicit comparison here is the derivation in the Fibonacci atomic relation volume; no originality claim is made.

## References

- Truth anchor: `D5/S3/Arith/Robin/EulerValuationMomentComparison.result`
- Dependency: [D5/S3/Arith/GoldenResource/ChainResponseSelectorGap](../GoldenResource/ChainResponseSelectorGap.md)
- Dependency: [D5/S3/Arith/GoldenResource/PrefixDeficitKernel](../GoldenResource/PrefixDeficitKernel.md)
