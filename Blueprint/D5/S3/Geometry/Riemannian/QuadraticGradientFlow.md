# A strictly convex gradient flow that is never a shortest connector

## Abstract

The anisotropic quadratic flow has a strict length and kinetic-action gap for every positive horizon.

Plane is EuclideanSpace Real (Fin 2) with its Euclidean inner product. point(u,v) is the corresponding vector, potential(p)=(p(0)^2+2*p(1)^2)/2, and flow(t)=point(exp(-t),exp(-2*t)). The metric, tangent norm, Riesz gradient and path length are the actual Euclidean/Riemannian objects.

**Theorem 1.1 (The actual flow derivative).**

Lean statement: `D5/S3/Geometry/Riemannian/QuadraticGradientFlow.flow_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Riemannian/QuadraticGradientFlow.flow_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t, flow has derivative point(-exp(-t),-2*exp(-2*t)) at t. This direct exponential-calculus helper is consumed by the actual gradient equation used in the strictness proof.

**Theorem 1.2 (A strict triangle along the parabola).**

Lean statement: `D5/S3/Geometry/Riemannian/QuadraticGradientFlow.parabola_strict_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Riemannian/QuadraticGradientFlow.parabola_strict_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a with 0<a<1, the norm of point(a^2,a^4)-point(1,1) is strictly smaller than the sum of the norms of point(a,a^2)-point(1,1) and point(a^2,a^4)-point(a,a^2). Equality in the Euclidean norm triangle would force proportional coordinate increments. Their determinant is a*(a-1)^3*(a+1), which is nonzero throughout the entire open interval. This is an arbitrary-parameter geometric inequality, with no finite sample or numerical certificate.

**Theorem 1.3 (Strict length and action gaps at every positive horizon).**

Lean statement: `D5/S3/Geometry/Riemannian/QuadraticGradientFlow.S8_actual_strict_length_and_nonattainment`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Riemannian/QuadraticGradientFlow.S8_actual_strict_length_and_nonattainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every T>0, pathELength IP flow 0 T is finite, its real value is strictly larger than the intrinsic distance between flow 0 and flow T, and kineticAction flow T is strictly larger than that distance squared divided by 2*ofReal(T). Put a=exp(-T/2), so 0<a<1. The points at 0,T/2,T are exactly point(1,1), point(a,a^2), point(a^2,a^4). The strict triangle, the two actual AC chord bounds and additivity of the speed integral give the strict length gap. The finite-energy length estimate then gives the strict action gap.

The potential is strictly convex on the whole plane. For p!=q and positive weights alpha,beta with alpha+beta=1, its convexity gap is (alpha*beta/2)*((p(0)-q(0))^2+2*(p(1)-q(1))^2)>0. Its actual Riesz gradient is point(p(0),2*p(1)); the potential and flow are C1, flow(0)=point(1,1), and the actual manifold derivative of flow at t is minus that gradient at flow(t). These facts follow from the coordinate Frechet derivative and the Riesz pairing. The exponential identity exp(-2*t)=exp(-t)^2 shows that every flow point lies on v=u^2.

Thus the same strictly convex potential, same initial state and actual gradient ODE supply the full original non-shortest-flow example, for every positive horizon. The argument concerns endpoint length and kinetic action in the stated geometry; it makes no assertion that arbitrary gradient flows minimize those quantities. The convexity calculation and parabola identity complete this application.

## References

- Truth anchor: `D5/S3/Geometry/Riemannian/QuadraticGradientFlow.S8_actual_strict_length_and_nonattainment`
- Truth anchor: `D5/S3/Geometry/Riemannian/QuadraticGradientFlow.flow_hasDerivAt`
- Truth anchor: `D5/S3/Geometry/Riemannian/QuadraticGradientFlow.parabola_strict_triangle`
- Dependency: [D5/S3/Geometry/Riemannian/GradientDissipation](GradientDissipation.md)
