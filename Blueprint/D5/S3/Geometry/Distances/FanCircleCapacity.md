# Fan's moving three-point circle capacity

## Abstract

The exact measure-theoretic definitions in Fan's moving three-point circle capacity conjecture.

**Definition 1.1 (The moving three-point set).**

Lean statement: `D5/S3/Geometry/Distances/FanCircleCapacity.points`

*Formalization.* `D5/S3/Geometry/Distances/FanCircleCapacity.points` (`✓ std3`).

*Citation.* Qiuling Fan (2026). *Riesz capacity ratios with negative exponents*. DOI: [10.48550/arXiv.2609.11186](https://doi.org/10.48550/arXiv.2609.11186). URL: <https://arxiv.org/abs/2609.11186v1>.

*Commentary.*

points(phi,psi) is the actual set of the three complex unit-circle points at polar angles psi, phi, and minus phi.

**Definition 1.2 (Positive-order energy).**

Lean statement: `D5/S3/Geometry/Distances/FanCircleCapacity.energy`

*Formalization.* `D5/S3/Geometry/Distances/FanCircleCapacity.energy` (`✓ std3`).

*Citation.* Qiuling Fan (2026). *Riesz capacity ratios with negative exponents*. DOI: [10.48550/arXiv.2609.11186](https://doi.org/10.48550/arXiv.2609.11186). URL: <https://arxiv.org/abs/2609.11186v1>.

*Commentary.*

energy(r,K,mu) is the double integral of dist(x,y)^r against a ProbabilityMeasure on the actual subtype K. Zero singleton masses are not excluded.

**Definition 1.3 (Negative-exponent Riesz capacity).**

Lean statement: `D5/S3/Geometry/Distances/FanCircleCapacity.capacity`

*Formalization.* `D5/S3/Geometry/Distances/FanCircleCapacity.capacity` (`✓ std3`).

*Citation.* Qiuling Fan (2026). *Riesz capacity ratios with negative exponents*. DOI: [10.48550/arXiv.2609.11186](https://doi.org/10.48550/arXiv.2609.11186). URL: <https://arxiv.org/abs/2609.11186v1>.

*Commentary.*

capacity(r,K) is the reciprocal-r power of the supremum of energy over all probability measures on K, matching Fan's convention for negative exponent minus r.

**Theorem 1.4 (The moving three-point capacity is maximal at the isosceles endpoint).**

Lean statement: `D5/S3/Geometry/Distances/FanCircleCapacity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Distances/FanCircleCapacity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Qiuling Fan (2026). *Riesz capacity ratios with negative exponents*. DOI: [10.48550/arXiv.2609.11186](https://doi.org/10.48550/arXiv.2609.11186). URL: <https://arxiv.org/abs/2609.11186v1>.

*Commentary.*

For every real r at least two and pi/2 < phi <= 2*pi/3, the capacity of the points at angles psi, phi and -phi is at most its value at psi = 2*pi - 3*phi whenever 0 <= psi <= 2*pi - 3*phi.

Proof. Put J=[0,2*pi-3*phi]. For t in J set x=(phi-t)/2 and y=(phi+t)/2. The stated bounds give 0<x<=y<=pi-phi<=pi/2 and x+y=phi. The chord formula dist(exp(is),exp(it))=2*abs(sin((s-t)/2)) therefore gives side lengths a=2*sin(x), b=2*sin(y), and c=2*sin(phi), with 0<a<=b<=c. Write A=a^r, B=b^r, C=c^r, and s=A+B-C.

The measure definition is not replaced by an assumed finite model. Mapping a ProbabilityMeasure on the actual point subtype along the subtype embedding gives an ambient probability measure concentrated on the three-point set and preserves the double integral. Conversely, restricting and pulling back any such ambient measure recovers a ProbabilityMeasure on the subtype. On this finite subtype, integration is the full sum over the three singleton masses u,v,w, including zero masses, so the energy is 2*C*u*v+2*A*v*w+2*B*w*u on the closed simplex u,v,w>=0 and u+v+w=1.

The classical three-point maximization is the two-branch computation of Clark and Laugesen, Theorem 8. If s<=0, the maximum is C/2, attained at (u,v,w)=(1/2,1/2,0). If s>0, let D=4*A*B-s^2. Then D>0 and the maximizing masses are u0=A*(B+C-A)/D, v0=B*(C+A-B)/D, and w0=C*(A+B-C)/D. They are nonnegative and sum to one. The value U=2*A*B*C/D is an upper bound because, after using w=1-u-v, its difference from an arbitrary simplex energy is ((2*B*(u-u0)+s*(v-v0))^2+D*(v-v0)^2)/(2*B). Thus the bound is attained, not merely a supremal estimate.

Both branches have the single form U=(C/2)*(4*A*B)/(4*A*B-max(s,0)^2). Since max(s,0)<=A and max(s,0)<=B, its denominator is at least 3*A*B>0. This formula identifies the exact supremum in the original ProbabilityMeasure capacity definition.

The power comparison needed on the active branch is as follows. For p>=1 and 0<=u<=v<=1 with u^p+v^p>=1, one has v-u<=v^p-u^p. The case p=1 is equality. Otherwise put alpha=1/p, s0=u^p, t0=v^p, delta=t0-s0, and z=(1-delta)/2. The endpoint cases delta=0,1 are immediate. For 0<delta<1, s0>=z. The function F(q)=(q+delta)^alpha-q^alpha is nonincreasing, while h(z)=z^alpha-(1-z)^alpha+1-2*z is concave and vanishes at both endpoints of [0,1/2]. Hence t0^alpha-s0^alpha<=F(z)<=(1-2*z)=delta. This is the concave-power argument used in Clark and Laugesen, Section 7.

Apply that inequality with p=r/2, u=a^2/c^2, and v=b^2/c^2. The side ordering gives 0<=u<=v<=1, and the active condition s>0 gives u^p+v^p>1. After clearing the positive powers of c, it yields C*(b^2-a^2)<=(B-A)*c^2. The trigonometric identities (cot(x)+cot(y))*sin(x)*sin(y)=sin(x+y) and (cot(x)-cot(y))*sin(x)*sin(y)=sin(y-x), together with x+y=phi, then show that (B+C-A)*cot(y)-(A+C-B)*cot(x)>=0.

Differentiate the unified profile rather than assuming an ordering of branch switches. Along the motion, A'=-(r/2)*A*cot(x) and B'=(r/2)*B*cot(y). The real function q(s)=max(s,0)^2 has derivative 2*max(s,0), including at zero: there abs(q(h)/h)<=abs(h). If s>0, the numerator governing the derivative is 2*r*A*B*s*((B+C-A)*cot(y)-(A+C-B)*cot(x)), which is nonnegative by the preceding comparison. If s<0 it is zero, and at s=0 the derivative of q is also zero. The positive denominator therefore gives a nonnegative derivative at every point of J.

The profile is continuous on J and differentiable in its interior, so the mean-value monotonicity theorem makes it nondecreasing. Its values are nonnegative, and r>0, so the increasing real power with exponent 1/r preserves the endpoint comparison. At t=2*pi-3*phi one has y=pi-phi and therefore b=c, giving exactly Fan's isosceles endpoint. The argument includes r=2 and phi=2*pi/3 and makes no strictness or uniqueness claim.

## References

- Truth anchor: `D5/S3/Geometry/Distances/FanCircleCapacity.capacity`
- Truth anchor: `D5/S3/Geometry/Distances/FanCircleCapacity.energy`
- Truth anchor: `D5/S3/Geometry/Distances/FanCircleCapacity.points`
- Truth anchor: `D5/S3/Geometry/Distances/FanCircleCapacity.result`
