# Reference Reserve at Finite Root Scales

## Abstract

The prime optimizer reserve has a uniform truncation tail at every finite root scale.

For x > 1 let lambda_x = 1/(x log x), v(x,p) = floor(log x/log p), g(x,p,a) = Q_a(1/p) - lambda_x a log p, and f(x,p,a) = log S_a(1/p) - lambda_x a log p. The prefixes S and Q are the finite geometric and harmonic power prefixes. For prime p define r(x,p) = g(x,p,v(x,p)) - sup_a f(x,p,a); for nonprime p put r(x,p) = 0. This is the function reserve in the theorem. Define R(x) as the sum of r(x,p) for natural p < ceil(x), and R_K(x) as the same sum restricted to p > x^(1/K). These are totalReserve and truncatedReserve. The vanishing of r(x,p) for p >= x makes these the full prime sum and the sum over x^(1/K) < p <= x respectively.

**Theorem 1.1 (Finite support, uniform tail, and retained exponent bound).**

$$\forall x \in \mathbb{R},\; 1 < x \Rightarrow \left(Finite\left(support\left(r\left(x\right)\right)\right) \land \left(\left(\forall p \in \mathbb{N},\; Prime\left(p\right) \Rightarrow \left(\exists a \in \mathbb{N},\; \left(\forall b \in \mathbb{N},\; f\left(x, p, b\right) \le f\left(x, p, a\right)\right) \land r\left(x, p\right) = g\left(x, p, v\left(x, p\right)\right)-f\left(x, p, a\right)\right)\right) \land \left(\left(\forall K \in \mathbb{N},\; 2 \le K \Rightarrow \left(0 \le R\left(x\right)-R_K\left(x\right) \land R\left(x\right)-R_K\left(x\right) \le (4+\frac{2}{K}) x^{\frac{-K}{K+1}}\right)\right) \land \left(\forall K \in \mathbb{N},\; \left(2 \le K \land K^{K} \le x\right) \Rightarrow \left(\forall p \in \mathbb{N},\; \left(Prime\left(p\right) \land x^{\frac{1}{K}} < p\right) \Rightarrow \left(\forall a \in \mathbb{N},\; \left(\forall b \in \mathbb{N},\; f\left(x, p, b\right) \le f\left(x, p, a\right)\right) \Rightarrow a \le K\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ReferenceReserve.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual supremum is attained. At every prime, its value and hence the reserve are independent of choices among tied maximizers. The k-th reference increment is nonnegative exactly when p^k <= x: after multiplying positive denominators this is the monotonicity of y log y. Consequently v(x,p) maximizes g. Comparing the logarithmic geometric prefix with Q gives 0 <= r(x,p) <= D_(v(x,p))(1/p). The finite-prefix deficit bound gives r(x,p) <= p^(-v(x,p)-1) < 1/x. When p >= x every reference increment is nonpositive, both maxima are zero, and the reserve vanishes.

Put t = x^(1/(K+1)). The omitted primes split into those at most t and those between t and x^(1/K). The first set has at most t members and each contributes at most 2/x. Every prime in the second set has reference exponent exactly K and contributes at most 2p^(-K-1). For an arbitrary finite set of integers above t >= 1, decreasing-power integral comparison bounds its sum of n^(-K-1) by (1+1/K)t^(-K). Combining the two sets and using t/x = t^(-K) gives (4+2/K)x^(-K/(K+1)).

If x >= K^K and p > x^(1/K), then p > K and log x < K log p < p log p. Thus p^(K+1) log p > x log x. The reciprocal-power marginal bound makes layer K+1 strictly unprofitable. Strict decrease of the marginals makes the actual objective strictly decreasing from K onwards, so every actual maximizer has exponent at most K.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/ReferenceReserve.result`
- Dependency: [D5/S3/Arith/GoldenLayerMarginalDecay](../GoldenLayerMarginalDecay.md)
- Dependency: [D5/S3/Arith/GoldenLocalThreshold](../GoldenLocalThreshold.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount](GoldenResourceOptimalLayerCount.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion](GoldenResourceThresholdCriterion.md)
- Dependency: [D5/S3/Arith/GoldenResource/PrefixDeficitKernel](PrefixDeficitKernel.md)
- Dependency: [D5/S3/Arith/GoldenResource/ReferencePrefixDominance](ReferencePrefixDominance.md)
- Dependency: [D5/S3/Arith/GoldenResourceOptimalInteger](../GoldenResourceOptimalInteger.md)
