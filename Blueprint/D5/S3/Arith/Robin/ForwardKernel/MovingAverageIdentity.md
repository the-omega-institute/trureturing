# Forward substitution for a moving increment average

## Abstract

A forward change of variables decomposes the average of E(x+s*x^a)-E(x) into three increment terms.

**Theorem 1.1 (The three-term forward identity).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingAverageIdentity.moving_average_forward_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingAverageIdentity.moving_average_forward_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be measurable and bounded on compact intervals, a>0, s>=0, x>0, and M>0. Write L(y)=s*y^a, Lprime(y)=s*a*y^(a-1), phi(y)=y+L(y), Q0=x+M+L(x), and delta=L(x+M)-L(x). Then M times the M-window average of the moving increment equals the integral of D_M E(x+r) from zero to L(x), minus the integral of Lprime(x+r)*(E(phi(x+r))-E(x)) from zero to M, plus the integral of E(Q0+v)-E(x) from zero to delta. Forward substitution uses the nonnegative derivative of phi. The fundamental theorem of calculus gives the integral of Lprime(x+r) as delta, so the constant E(x) cancels between the two correction terms. No continuity or derivative of E is required.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingAverageIdentity.moving_average_forward_identity`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs](CrossExponentDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer](VarianceTransfer.md)
