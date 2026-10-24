# The remainder tail at the infinite endpoint

## Abstract

The forward-kernel remainder estimates imply convergence and holomorphy of the Chebyshev partial-summation tail.

**Theorem 1.1 (An integrable differentiated tail and a vanishing boundary).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernelRemainderContinuation.remainder_tail_converges`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernelRemainderContinuation.remainder_tail_converges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put E(t)=psi(t)-t and assume that there is a real C satisfying |E(t)|<=C*sqrt(t)*log(t)^2 for every t>=2. Let x0>=3, sigma>-1/5 and A>=0. Suppose complex-valued functions r and dr satisfy |r(t)|<=A*t^(-sigma-7/10) and |dr(t)|<=A*t^(-sigma-17/10) for t>=x0, with dr almost everywhere strongly measurable on (x0,infinity). Then E(t)*dr(t) is absolutely integrable there, and E(t)*r(t) tends to zero as t tends to infinity.

Choose eta=(sigma+1/5)/4. The elementary logarithmic estimate gives |E(t)|<=(C/eta^2)*t^(1/2+2*eta). Multiplication by the two assumed kernel bounds gives a boundary majorant proportional to t^p and an integral majorant proportional to t^(p-1), where p=-sigma-1/5+2*eta=-(sigma+1/5)/2<0. These two real-power estimates prove the conclusions. For partial summation, dr may be the derivative of r. The theorem only uses the displayed estimates and measurability; it does not assert that the actual adjoint kernel satisfies them or that its integral is holomorphic.

**Theorem 1.2 (A holomorphic integral under compact parameter bounds).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernelRemainderContinuation.remainder_integral_holomorphic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernelRemainderContinuation.remainder_integral_holomorphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the same von Koch bound and x0>=3. Let d(s,t) be holomorphic in s on Re(s)>-1/5 for each t>x0, and assume that d(s,t) and its complex parameter derivative are almost everywhere strongly measurable in t for each such s. Suppose every compact set K in this half-plane has a constant A>=0 such that |d(s,t)|<=A*t^(-Re(s)-17/10) for all s in K and t>=x0. Then integral_(x0,infinity) E(t)*d(s,t) dt is holomorphic on Re(s)>-1/5.

At a fixed parameter s choose r=(Re(s)+1/5)/4. The closed ball of radius 2*r about s lies in the half-plane. Throughout this ball Re(z)>=sigma=Re(s)-2*r>-1/5. For y within radius r of s, Cauchy's estimate on the circle of radius r about y bounds the parameter derivative of d(y,t) by (A/r)*t^(-sigma-17/10). The preceding convergence theorem makes this bound integrable after multiplication by |E(t)|. Differentiation under the Lebesgue integral proves the conclusion. This theorem applies to a family once its stated kernel estimates and regularity are supplied; it does not supply those estimates for the actual adjoint kernel.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernelRemainderContinuation.remainder_integral_holomorphic`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernelRemainderContinuation.remainder_tail_converges`
- Dependency: [D5/S3/Arith/Robin/ForwardKernelMellinConvergence](ForwardKernelMellinConvergence.md)
