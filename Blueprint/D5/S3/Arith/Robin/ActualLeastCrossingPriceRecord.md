# Uniform Positive-Price Predecessor Records

## Abstract

Actual least Robin-height crossings confine every occupied prime layer at a uniform positive price.

**Theorem 1.1 (One threshold through eta equal to one half).**

Lean statement: `D5/S3/Arith/Robin/ActualLeastCrossingPriceRecord.uniform_actual_least_crossing_price_record`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualLeastCrossingPriceRecord.uniform_actual_least_crossing_price_record` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W(n)=log(sigma(1,n)/n), F(n)=W(n)-log(log(log(n))), and H(eta,n)=(log(n))^eta*(F(n)-gamma), with the existing total real definitions. There is T0>0, chosen before eta, such that for every 0<eta<=1/2, every T>=T0, and every actual m>=3 with H(eta,m)>=T and H(eta,n)<T for all 3<=n<m, put X=log(m), L=log(X), c=39/20, lambda=(1-c*eta)/(X*L) and lambda0=1/(40*X*L). Both prices are positive. At each price m strictly beats every positive predecessor n<m for the literal goldenResourceObjective. Every prime p and 1<=j<=v_p(m) satisfies p^j*log(p)<40*X*L. Moreover m divides ActualTwoPriceDefect.strictInteger(lambda0), and 5040 divides m.

The arbitrary-error envelope in ActualIntegerLogEnvelope is used with epsilon=1/20, giving F(n)-gamma<=(39/20)/log(log(n)) for all sufficiently large actual n. No support condition is imposed on n. With R=max(A,exp(2),log(30)), the shared uniform_actual_height_escape at R+1 chooses T0 independently of eta and ensures W(m)>R+1 and X>=exp(2). Put a=1-c*eta. Then 1/40<=a<=1 and lambda*X<=1. A hypothetical price rival has W(n)>=W(m)-1>R. The elementary divisor_log_le_log bound puts log(n)>R before the improved envelope is used. This proves n>=3 and log(log(n))>=2; the statement still compares all positive predecessors, including one and two.

For l>=2, beta>0 and 0<eta<=1/2, the strict scalar remainder is log(1+beta/l)-(c/l)*(1-exp(-eta*beta))>(1-c*eta)*beta/(l+beta). Differentiate the difference of these two sides. Writing b=c*eta and t=beta/l, its derivative numerator is exp(eta*beta)*(b+t)-b*(1+t)^2. The exponential tangent gives exp(eta*beta)>1+b*t, while (b+t)*(1+b*t)-b*(1+t)^2=t*(1-b)^2>=0. Thus the derivative is strictly positive away from zero, where the difference vanishes.

For the rival put Y=log(n), l=log(Y), beta=log(X)-log(Y), E=F(n)-gamma and delta=W(m)-W(n). The rival bounds delta by a*(1-exp(-beta))/L<a*beta/L. The scalar remainder and E<=c/l then make delta+E*(1-(Y/X)^eta)-log(L/l) strictly negative, even when E is negative. The exact literal height cancellation gives H(eta,m)<H(eta,n), contradicting leastness. Lowering lambda to lambda0 preserves strictness because log(n)<X.

For every occupied prime p use the actual proper positive quotient m/p. The public single-layer objective identity and exact factorization arithmetic give lambda0<goldenLayerMarginal(p,v_p(m)). The existing strict_layer_iff places this exponent, and hence every smaller occupied layer, in the same canonical strictInteger(lambda0). Coordinatewise factorization comparison proves divisibility. The reciprocal-power marginal bound gives the literal strict cutoff. Positive-price records also give strict abundancy records; W(m)>log(30) permits the existing 5040 theorem to apply.

This combines the repository's arithmetic and analytic results with a quantitative scalar estimate; no literature priority is claimed. No crossing existence, height unboundedness, signed upper bound, Robin inequality or RH follows here. The conclusion compares predecessors only. It supplies neither global optimality of m, conditions on absent layers nor equality with the strict inventory. The full RH goal and its signed-upper and unboundedness gaps remain open.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualLeastCrossingPriceRecord.uniform_actual_least_crossing_price_record`
- Dependency: [D5/S3/Arith/Robin/ActualLeastCrossing5040](ActualLeastCrossing5040.md)
- Dependency: [D5/S3/Arith/Robin/ActualTwoPriceDefect](ActualTwoPriceDefect.md)
