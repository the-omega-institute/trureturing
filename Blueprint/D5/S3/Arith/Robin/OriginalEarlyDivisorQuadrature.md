# Early Divisor Quadrature of the Original Kernel

## Abstract

The early divisor rows of the original Robin kernel have an exact signed endpoint and a decaying smooth remainder.

Audit disclosure: the new weighted_bernoulli_phase registration compiles but remains declared_unresolved at IE-C050/source.selection_missing. Missing source-coordinate/readout selection and current binding evidence are tracked at https://github.com/the-omega-institute/trureturing/issues/17898. The finite analytic proof and unfinished audit have distinct scopes.

Let lambda(x)=1/(x log(x)), w(x)=-lambda'(x), H=t^(4/5), B=t+H, c=w(t)t^(11/10), and D=floor(t^(151/500)). Use the original kernel (lambda(x)-lambda(B))/c for t<x<=B, and zero elsewhere. The positive cofactor row Z_t(d) sums log(m)k_t(dm) through floor(B/d); Y_t(d) is d^(-1) integral from t to B of log(x/d)k_t(x). All positive d<=D are retained with the actual integer Mobius coefficient, including its zero values and m=1.

**Theorem 1.1 (Centered primitive and arbitrary real endpoint phases).**

Lean statement: `D5/S3/Arith/Robin/OriginalEarlyDivisorQuadrature.weighted_bernoulli_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalEarlyDivisorQuadrature.weighted_bernoulli_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 1<a<=b, translate the same periodic primitive by -1/48: P(t)=(fract(t)-1/2)^2/2-1/16. Its absolute value is at most 1/16. Constant translation preserves continuity through integer seams and the right derivative beta(t)=fract(t)-1/2, including integer endpoints.

For the original density k and its original derivative k', E=integral_a^b k(t)beta(t)=k(b)P(b)-k(a)P(a) -integral_a^b k'(t)P(t). Hence |E-k(b)P(b)+k(a)P(a)|<=(k(a)-k(b))/16 and |E|<=k(a)/8. The negative increasing slope bound is -v(a)/8; the original -v(a)/6 statement remains valid. The same integration by parts proves both estimates. No integer-endpoint restriction or positivity conclusion for a full arithmetic discrepancy is imposed.

**Theorem 1.2 (A signed endpoint and the full smooth remainder).**

Lean statement: `D5/S3/Arith/Robin/OriginalEarlyDivisorQuadrature.original_early_quadrature`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalEarlyDivisorQuadrature.original_early_quadrature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t>=256, set b=(lambda(t)-lambda(B))/c and beta(y)=Int.fract(y)-1/2. Then E_early=sum_{1<=d<=D} mu(d)(Z_t(d)-Y_t(d)) equals b Q_D plus its smooth residual, where Q_D=sum_{1<=d<=D} mu(d)log(t/d)beta(t/d). The residual has absolute value at most (1/6)sum_{1<=d<=D}|mu(d)|d [log(t/d)t^(-11/10)-b/t], and hence at most t^(-62/125)log(t)/6. Every displayed bracket is nonnegative.

The finite all-power readout Phi is sum_{1<=n<=floor(B)} Lambda(n)k_t(n)-a(t), with a(t)=[log(log(B))-log(log(t))-H lambda(B)]/c. Finite Mobius convolution gives Phi=G+E_early, where G retains the integrated early rows and every remaining original discrete row. Therefore the same residual bound applies to Phi-G-b Q_D. Each reference prime power keeps its full von Mangoldt mass.

The smooth body log(x/d)(lambda(x)-lambda(B))/c extends to the excluded initial point. Its derivative is nonpositive and increasing on [t,B]. The continuous periodic primitive [fract(y)^2-fract(y)+1/6]/2 has right derivative beta(y), also at integers, and absolute value at most 1/12. Two integrations by parts give the original initial-slope bound. Thus beta(j)=-1/2 at every integer j, while the terminal kernel weight is zero.

This estimate bounds the smooth residual. Decay of the full E_early requires a further cancellation estimate for Q_D. The finite Phi definition is the all-power readout in the integrated-weight source; identifying its integral with the native selected-family psi integral requires the separate finite-step and integration assembly. No favorable signed mean or all-integer Robin inequality follows from this residual estimate.

Euler-Maclaurin is reused from the native real-endpoint supplier in ZetaPntBase.EulerMaclaurin. The price, weight and price-drop facts are reused from ActualRobinClockCovariance, MellinWeightedVariation and OriginalMovingWindowMoment. The original arithmetic definitions occur in the integrated weights section of Nicolas2025Comparison. The periodic Bernoulli construction follows the classical Euler-Maclaurin method (DLMF 2.10.1).

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalEarlyDivisorQuadrature.original_early_quadrature`
- Truth anchor: `D5/S3/Arith/Robin/OriginalEarlyDivisorQuadrature.weighted_bernoulli_phase`
- Dependency: [D5/S3/Arith/Robin/OriginalMovingWindowMoment](OriginalMovingWindowMoment.md)
