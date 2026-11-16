# Uniform continuous weighted cross moments

## Abstract

Under the two variance band asymptotics with a<b, every continuous real function phi on [1,2] satisfies uniform convergence to zero of the dyadic expectation of phi(x/X) B_a(s,x) B_b(t,x). The two second moment bounds control absolute logarithmic mass, and continuous weight approximation extends uniform subinterval cancellation to phi.

**Theorem 1.1 (Uniform cross interval cancellation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_interval_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_interval_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a<b lie in two valid variance bands for the same locally bounded Borel function. The integral of D_(s*x^a)(x) D_(t*x^b)(x) over any subinterval of [X,2X], divided by X^(1+(a+b)/2) log(X), tends to zero uniformly over s,t in [0,1] and both endpoints. Intermediate powers X^mu and X^nu inside the first variance band and below b make each of the three ratios in the four-scale covariance bound tend to zero.

**Theorem 1.2 (Normalized cross moments on subintervals).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_weighted_interval_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_weighted_interval_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same two bands and a<b, the integral of B_a(s,x) B_b(t,x)/x tends to zero uniformly over both time parameters and all dyadic subintervals. The reciprocal weight is x^(-1-(a+b)/2)/log(x), and the shared decreasing-weight estimate transfers the raw interval bound.

**Theorem 1.3 (Uniform continuous weighted cross moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_moment_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_moment_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the two variance band asymptotics with a<b, every continuous real function phi on [1,2] satisfies uniform convergence to zero of the dyadic expectation of phi(x/X) B_a(s,x) B_b(t,x). The two second moment bounds control absolute logarithmic mass, and continuous weight approximation extends uniform subinterval cancellation to phi.

**Theorem 1.4 (The cross-moment interface).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_moment_interface`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_moment_interface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two variance bands containing a<b, the joint first-first interface has identically zero kernel. The larger of the two uniform second absolute-moment bounds controls both exponents. Choosing the continuous weight u to the power (1-a)/2+(1-b)/2 in the weighted cross limit gives the mixed-moment limit at every point of the closed unit square.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_interval_cancellation`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_moment_interface`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_moment_uniform`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.cross_weighted_interval_cancellation`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface](FirstOrderInterface.md)
