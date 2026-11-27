# The exact optimized entropy asymptotic

## Abstract

The exact entropy coefficient of the actual optimized compact factorial family.

Write h for binary entropy. On [0,1], h(v)=h(min(v,1/2))+h(max(v,1/2))-log 2. The first clipped term is increasing and the second is decreasing. Monotone left and right sum comparisons therefore give |sum over i<r of h(ti/r)+r I(t)|<=2 log 2, uniformly for 0<=t<=1, including the endpoints.

The finite Stirling estimate then compares log S_b with rs(log s-1+I(rb/s))+rb log r, with error 2r(log(s+1)+1)+2s log 2. The minimum property of I gives the lower bound for every legal parameter. To obtain an upper bound choose b as the floor of t* times s/r, where t* is the continuous minimizer. Then rb<=s and 0<=t*-rb/s<r/s. Convexity along the segment from zero to t* gives I(rb/s)-I(t*)<=kappa r/(s t*). Consequently some legal term is at most rs(log s-1-kappa) plus the same error, s log r and (kappa/t*)r^2.

For M>=2, rs/M=M^2-1. The inequalities -2/M<=log(1-1/M)<=0 and log(s+1)<=2 log(M+1) control the change from s to M^2. After division by M all errors are bounded by C M(log(M+1)+1). The attained finite minimum and the uniform lower bound give both directions of the claimed asymptotic.

**Definition 1.1 (The continuous optimizing parameter).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.entropyOptimizer`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.entropyOptimizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unique minimizer t* of I on [0,1] exists by the continuous entropy profile. It is positive: I(0)=0 while I(1)=-1/2. No strict upper bound t*<1 is required.

**Definition 1.2 (The optimized entropy constant).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.kappa`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set kappa=-I(t*). The profile bound gives 1/2<=kappa<=log 2-1/8<gamma.

**Definition 1.3 (The legal finite parameter set).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.legalParameters`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.legalParameters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For M natural, r=M+1 and s=M(M-1). The legal set contains all natural b with rb<=s. Since r>=1 each legal b is at most s, so filtering the range from zero to s omits none. Zero is always legal.

**Definition 1.4 (The factorial benchmark).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.windowLoss`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.windowLoss` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The term loss is log(S_b(M+1,M(M-1)))/M-h0(M^2), where h0(x)=x log x-(1+gamma)x. Natural subtraction in s is retained also for M=0 and M=1. The asymptotic estimate applies for M>=2.

**Definition 1.5 (The actual finite minimum).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.minimumLoss`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.minimumLoss` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the finite infimum of the term loss over the nonempty legal parameter set. This minimum is attained by a legal natural parameter.

**Theorem 1.6 (The exact optimized quadratic coefficient).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.optimized_entropy_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.optimized_entropy_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every M>=2, every legal term loss is at least (gamma-kappa)M^2-C M(log(M+1)+1), with C=32+4 kappa/t*. A legal parameter attains the actual finite minimum, and its difference from (gamma-kappa)M^2 has absolute value at most C M(log(M+1)+1). Thus the coefficient of the actual optimized family is exactly gamma-kappa, and this coefficient is positive.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.entropyOptimizer`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.kappa`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.legalParameters`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.minimumLoss`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.optimized_entropy_asymptotic`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy.windowLoss`
- Dependency: [D5/S3/Arith/FactorialRatio/Compression/EntropyProfile](EntropyProfile.md)
