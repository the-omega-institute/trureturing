# Two moving endpoints

## Abstract

Comparable cumulative variances control increments between two increasing endpoints.

**Theorem 1.1 (The two-endpoint square estimate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance.two_endpoint_increment_square_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance.two_endpoint_increment_square_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be Borel measurable and locally bounded. Let p and q be continuous on [l,r], l<=r, with derivatives within that interval bounded below by m>0. Assume their images lie in [1,Y], 0<=q(x)-p(x)<=C0*R, R>0, C0>=0, and K>=0. If V(Y,u)<=K for every R<=u<=(C0+2)*R, then the integral of (E(q(x))-E(p(x)))^2 over [l,r] is at most 2*(C0+2)*K/m.

Put delta=q(x)-p(x). Average the identity E(q(x))-E(p(x))=D_v(p(x))-D_(v-delta)(q(x)) over (C0+1)*R<=v<=(C0+2)*R, and use (A-B)^2<=2*A^2+2*B^2. Translation enlarges the second length interval to [R,(C0+2)*R]. Fubini and change of variables through p and q bound the two averaged terms by R*K/m and (C0+1)*R*K/m. Division by R gives the claim. Only differentiability and a positive lower derivative bound are needed; derivative continuity is unnecessary.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance.two_endpoint_increment_square_le`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer](VarianceTransfer.md)
