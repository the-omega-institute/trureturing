# Signed forward-kernel remainders

## Abstract

Partial summation identifies a convergent signed prime-power remainder with its error integral.

**Theorem 1.1 (The infinite endpoint of exact partial summation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernelSignedRemainder.signed_remainder_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernelSignedRemainder.signed_remainder_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E(t)=psi(t)-t and assume |E(t)|<=C*sqrt(t)*log(t)^2 for t>=2. Suppose a>=3, sigma>-1/5, A>=0, r'=dr on [a,infinity), and dr is continuous there. If |r(t)|<=A*t^(-sigma-7/10) and |dr(t)|<=A*t^(-sigma-17/10), then as b tends to infinity, sum(Lambda(n)*r(n),floor(a)<n<=floor(b))-integral_a^b r(t) dt tends to -E(a)*r(a)-integral_a^infinity E(t)*dr(t) dt.

Finite Abel summation and ordinary integration by parts give the exact identity with the additional endpoint E(b)*r(b). The complete Chebyshev psi keeps every prime power with its full logarithmic weight. The initial atom is excluded and the terminal atom is included. The stated estimates make the error integral absolutely integrable and send the terminal endpoint to zero.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernelSignedRemainder.signed_remainder_tendsto`
- Dependency: [D5/S3/Arith/Robin/ForwardKernelRemainderContinuation](ForwardKernelRemainderContinuation.md)
