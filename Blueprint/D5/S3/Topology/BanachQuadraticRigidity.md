# Banach quadratic rigidity

## Abstract

Symmetric bilinear exponential-isometry rigidity in an arbitrary real Banach space.

**Theorem 1.1 (Two solutions preserve distance).**

Lean statement: `D5/S3/Topology/BanachQuadraticRigidity.quadratic_solution_dist_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/BanachQuadraticRigidity.quadratic_solution_dist_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be any complete real normed vector space, including the zero space, and B a continuous real bilinear map from E times E to E. Suppose B is symmetric and, for every x in E and every real h, the exponential of h times the operator B(x,-) is an isometry in the given norm. On any open connected subset s of the real line, let x and y both solve z'=B(z,z) at every time in s. Then dist(x(t),y(t)) equals dist(x(u),y(u)) for every t,u in s. No finite dimension, inner product, nonzero carrier or supplied global flow is assumed.

At a fixed time v freeze A=B(x(v)+y(v),-). Bilinearity and symmetry give (x-y)'(v)=A(x(v)-y(v)). The frozen orbit exp((w-v)A)(x(v)-y(v)) has the same value and derivative at v. Their difference is o(|w-v|). The reverse triangle inequality bounds the change of norms by this difference, while exponential isometry makes the orbit norm constant. Thus the norm of x-y has derivative zero, even when the ambient norm is not differentiable. The mean value theorem on the open connected time domain gives the asserted distance identity. The exponential derivative and mean value theorem are used directly from pinned Mathlib.

**Theorem 1.2 (All exponential isometries force the bilinear map to vanish).**

Lean statement: `D5/S3/Topology/BanachQuadraticRigidity.eq_zero_of_symmetric_exp_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/BanachQuadraticRigidity.eq_zero_of_symmetric_exp_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real Banach space E and every continuous real bilinear B:E times E to E, if B is symmetric and exp(t B(x,-)) is an isometry for every x in E and every real t, then B=0. The given norm is arbitrary. The theorem includes zero spaces and arbitrary dimension and assumes no flow, linearity of a flow, inner product or nontrivial carrier.

Mathlib local existence for the continuously differentiable quadratic field supplies a common local solution time near zero. For initial x scale the state by a=r/(1+norm(x)), where r is the local radius. Distance conservation against the zero solution keeps the scaled solution norm equal to a norm(x). Scale its value by a inverse and its time by r inverse. This supplies the normalized field f(x)=B(x,x)/(1+norm(x)) on the same positive time interval for every state. The frozen UniformLocalGlobalPasting theorem is applied directly with this uniform all-state interval, producing a global normalized solution. Its norm is constant by the frozen-orbit comparison. Rescaling time by 1+norm(x) gives a global solution of the original quadratic equation.

Choose one such solution for each initial state. Distance conservation proves uniqueness and the autonomous composition law. Negative time provides an actual inverse, so each time map is a surjective isometry fixing zero. Apply Mathlib's IsometryEquiv.toRealLinearIsometryEquivOfMapZero directly. Differentiating its scalar-two identity at time zero yields 4 B(x,x)=2 B(x,x), so B vanishes on the diagonal. Bilinearity and symmetry then polarize this identity to B(x,y)=0.

The intended source application is the quadratic-flow step after (2.8) in AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE. It uses the same completed space, the same original symmetric S, K=T-I, and B(a,b)=K(S(a,b))-S(K(a),b)-S(a,K(b)). Once that B and its exponential isometry hypotheses are supplied, the theorem applies to any two of its actual quadratic solutions on their common open time interval. The full rigidity theorem then gives this same B=0, hence K(S(a,b))=S(K(a),b)+S(a,K(b)) for every a,b. This is the same-S derivation identity, conditional on supplying the source-specific bounded bilinear map and its exponential-isometry hypotheses.

This result supplies the arbitrary Banach quadratic-rigidity subargument. Constructing the source-specific B from the same S and K, proving its exponential isometries from the original order data, integrating the same-S derivation identity to (2.9), constructing the actual operators A_h, and deriving K=0 and the original unit law remain separate source bridges. The already formalized dominated scalar operator rigidity is not reproved here.

## References

- Truth anchor: `D5/S3/Topology/BanachQuadraticRigidity.eq_zero_of_symmetric_exp_isometry`
- Truth anchor: `D5/S3/Topology/BanachQuadraticRigidity.quadratic_solution_dist_eq`
- Dependency: [D5/S3/Geometry/ODE/UniformLocalGlobalPasting](../Geometry/ODE/UniformLocalGlobalPasting.md)
