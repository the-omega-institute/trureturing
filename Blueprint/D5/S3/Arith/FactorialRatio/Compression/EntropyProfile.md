# Entropy of the compact factorial grid

## Abstract

The continuous entropy minimum and a uniform obstruction for a single compact factorial term.

**Definition 1.1 (The signed continuous average).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.entropyIntegral`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.entropyIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real parameter t, I(t) is the integral from zero to one of -h(tu), where h(v)=-v log v-(1-v)log(1-v) is binary entropy. The convention v log v=0 at zero includes both endpoints.

**Theorem 1.2 (Strict convexity of the signed average).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.profile_strictConvex`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.profile_strictConvex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed entropy average is strictly convex on [0,1]. Strict concavity of binary entropy gives the pointwise convexity inequality after changing sign. For distinct parameters the inequality is strict at u=1/2, and continuity makes the integral inequality strict. Its convexity also bounds the error from rounding a minimizing parameter downward along the segment joining it to zero.

**Theorem 1.3 (Closed form, unique minimum and the strict gamma gap).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.entropy_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.entropy_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

I is continuous, I(0)=0 and I(1)=-1/2. For 0<t<=1 it equals (t/2)log t-((1-t)^2/(2t))log(1-t)-1/2. There is exactly one minimizer on the closed interval [0,1]. For every parameter in that interval, I(t)>=-(log 2-1/8) and gamma+I(t)>0. Thus kappa=-min I is strictly smaller than gamma.

An endpoint-continuous primitive is [v^2 log v-(1-v)^2 log(1-v)-v]/2. Scaling its integral gives the closed form. Strict concavity of h, integrated on any nontrivial segment, gives strict convexity of I and uniqueness of the minimum. The corrected entropy h(v)+2(v-1/2)^2 is concave, symmetric and maximal at one half. Consequently h(v)<=log 2-(2v-1)^2/2. Its integrated majorant is log 2-1/2+t-2t^2/3, at most log 2-1/8. The certified logarithm and Euler constant brackets make the final gap strict.

**Theorem 1.4 (A finite lower bound uniform in the legal parameter).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.compact_single_term_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.compact_single_term_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural r,s,b with rb<=s, the logarithm of S_b(r,s)=product over 0<=i<r of ((i+1)b)!/b! times (s-ib)! is at least rs(log s-1-41/72)-2r(log(s+1)+1). This includes zero parameters and zero factorial arguments.

The quadratic entropy majorant also controls the actual finite grid. If w>=0 and rw<=1, its sum is at most r(log 2-1/8). The difference from that bound is exactly r(4rw-3)^2/24+rw(1-rw)+rw^2/3, a sum of nonnegative terms. Set w=b/s, treating s=0 separately. The inequality log 2-1/8<41/72 and the finite Stirling estimate give the stated bound after omitting the nonnegative rb log r term. No unproved comparison with an integral is required.

**Theorem 1.5 (Every single term has a positive quadratic loss).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.quadratic_window_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.quadratic_window_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M>=2, r=M+1, s=M(M-1), and let b be any natural parameter with (M+1)b<=M(M-1). Write x=M^2 and h0(x)=x log x-(1+gamma)x. Then gamma-41/72>0 and log(S_b(r,s))/M-h0(x) is at least (gamma-41/72)M^2-8M(log(M+1)+1). The error is explicit and uniform over the entire legal grid.

The logarithm inequality log(1-1/M)>=-2/M controls the change from s to M^2. Also log(s+1)<=2 log(M+1) and 2(M+1)/M<=3. Combining these estimates with the finite single-term bound gives the displayed error. This concerns selection of one compact-family term; the primewise gains obtained by a gcd use different terms at different primes.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.compact_single_term_lower_bound`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.entropyIntegral`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.entropy_profile`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.profile_strictConvex`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/EntropyProfile.quadratic_window_obstruction`
- Dependency: [D5/S3/Arith/FactorialRatio/Compression/StirlingBarrier](StirlingBarrier.md)
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](../../GoldenResource/RobinRationalBasis.md)
