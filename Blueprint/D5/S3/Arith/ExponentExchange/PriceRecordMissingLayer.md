# Missing Layers at Full Price Records

## Abstract

A full predecessor record at positive price controls the missing next layer at every prime smaller than any prime divisor of the record integer.

**Theorem 1.1 (A strict exchange bound and a uniform logarithmic Euler tail).**

Lean statement: `D5/S3/Arith/ExponentExchange/PriceRecordMissingLayer.price_record_missing_layer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/PriceRecordMissingLayer.price_record_missing_layer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be a positive natural number and lambda a positive real number. Assume the literal goldenResourceObjective at m is strictly larger than at every positive natural number n < m, including 1 and 2 whenever they precede m. Let P be any prime divisor of m and q any prime with q < P. Write vP = Nat.factorization m P, vq = Nat.factorization m q, u = m/P, n = u*q, and r = (1/q)^(vq+1). Then 0 < n < m, u*P = m, Nat.factorization u P + 1 = vP, and Nat.factorization u q = vq. In particular vP >= 1, while vq may be zero.

With M(p,k) denoting the existing goldenLayerMarginal, the strict comparison is M(q,vq+1)*log(q) + lambda*(log(P)-log(q)) < M(P,vP)*log(P). The last P layer satisfies M(P,vP)*log(P) <= 1/P. Since the price correction is positive, M(q,vq+1)*log(q) < 1/P. Moreover 0 < r <= 1/q <= 1/2 and -log(1-r) < 2/P.

Apply the single-layer objective delta at u with P and q and subtract. The full predecessor comparison at the actual replacement n yields the strict gain inequality. The reciprocal-power marginal estimate at vP bounds the last P gain by (1/P)^vP <= 1/P.

The same literal q gain is log((1-r/q)/(1-r)). For x = 1/q <= 1/2, (1-r*x)^2-(1-r) = r*(1-2*x)+(r*x)^2 >= 0. Both 1-r and 1-r*x are positive. Monotonicity of the logarithm and its quotient identity therefore give -log(1-r) <= 2*log((1-r/q)/(1-r)), which combines with the strict gain bound. This is a finite consequence for a given full price record; it requires neither initial prime support nor global optimality and asserts neither existence of such records nor the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Arith/ExponentExchange/PriceRecordMissingLayer.price_record_missing_layer`
- Dependency: [D5/S3/Arith/GoldenLayerMarginalDecay](../GoldenLayerMarginalDecay.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison](../GoldenResource/GoldenResource5040EndpointComparison.md)
