# The shared mixed-coordinate comparison

## Abstract

The exact six-variable formula, mixed-coordinate monotonicity and a shared-center inverse-angle application.

All variables below are real numbers. Icc(a,b) denotes the closed interval [a,b]. In the local edge order (12,13,14,34,24,23), the inputs (x,y,z,o,v,w) keep all six coordinates independent. Coordinates x and o are opposite.

Define rad(x,y,z)=2xyz+x^2+y^2+z^2-1 and P(x,y,z,o,v,w)=yz+vw+xyv+xzw-(x^2-1)o. The function cosine is P divided first by sqrt(rad(x,y,w)) and then by sqrt(rad(x,z,v)). This is the exact six-variable formula used by the cited source. Both radicands are proved positive on the box.

The inverse-angle application uses a different parameter domain from the comparison theorem below. Its six angles have the original order (12,13,14,34,24,23)=(theta,a,b,g,c,d). Set z=cos(theta), D(theta,alpha,beta)=rad(z,cos(alpha),cos(beta)) and I=cosine(z,cos(a),cos(d),cos(g),cos(c),cos(b)). The permutation of the third and sixth inputs retains the original endpoint triples. The comparison theorem on [1,2] is not applied to these cosine inputs.

Assume theta,a,b,c,d>0, theta+a+b<pi and theta+c+d<pi; g may be any real number. Both D(theta,a,b) and D(theta,c,d) are positive. Expanding the existing numerator and using sin(theta)^2=1-z^2 writes I as [sin(theta)^2 cos(g)+cos(a)cos(d)+cos(b)cos(c)+z(cos(a)cos(c)+cos(b)cos(d))]/sqrt(D(theta,a,b)D(theta,c,d)). The same scalar expression occurs in Frigerio-Moraschini, On volumes of truncated tetrahedra with constrained edge lengths, arXiv:1801.05326v3, Section 1.1, formulas (1), (3) and (4), https://arxiv.org/html/1801.05326v3.

For one endpoint split (alpha,beta), put k=cos(alpha+beta), h=cos(alpha-beta), A=z+k, C=cos(alpha)+cos(beta) and E=cos(alpha)-cos(beta). Strict decrease of cosine on [0,pi] gives A>0 from alpha+beta<pi-theta. Sine positivity gives h-k=2sin(alpha)sin(beta)>0, while -1<z<1 and -1<=k<=1. Cosine addition and subtraction and sin^2+cos^2=1 give D=A(z+h), C^2=(1+k)(1+h) and E^2=(1-k)(1-h). Consequently D-A^2=A(h-k)>0, so sqrt(D)>A and D>0.

The squared coordinate gaps factor as (1+k)^2D-A^2C^2=A(1+k)(1-z)(h-k)>=0 and (1-k)^2D-A^2E^2=A(1-k)(1+z)(h-k)>=0. All factors have the indicated signs. Comparing nonnegative squares therefore gives A|C|<=(1+k)sqrt(D) and A|E|<=(1-k)sqrt(D). These estimates use the same z at both endpoints; they do not optimize unrelated endpoint states.

Apply the estimates to (a,b) and (d,c). Write k1=cos(a+b), k2=cos(c+d), A=z+k1, B=z+k2, S=sin(theta)^2 and R=sqrt(D(theta,a,b)D(theta,c,d)). Then R>AB>0 and S>0. Take C1=cos(a)+cos(b), C2=cos(d)+cos(c), E1=cos(a)-cos(b) and E2=cos(d)-cos(c). The numerator N is S cos(g)+(1+z)C1C2/2+(1-z)E1E2/2. In particular, the sign of E2 is fixed by the original six-slot pairing.

Multiplication of the two endpoint bounds and use of the nonnegative weights (1+z)/2 and (1-z)/2 gives AB[N-S cos(g)]<=R[1+k1 k2+z(k1+k2)]=R(AB+S). Since cos(g)<=1 and R>AB with S>0, AB N<=AB S+R(AB+S)<R(AB+2S). Dividing by positive AB and R yields the strict shared-center bound I<1+2sin(theta)^2/[(cos(theta)+cos(a+b))(cos(theta)+cos(c+d))]. This includes obtuse theta and arbitrary g; it assumes no equality of endpoint angles.

The full genuine-angle domain additionally imposes g>0, a+d+g<pi and b+c+g<pi, so it is contained in the scalar domain just used. The trigonometric, product-order and square-root facts combine to give this application of the existing expression. It is distinct from the mixed-coordinate comparison theorem below. Identification of I with cosh of an actual native edge length remains a separate geometric requirement; neither a tetrahedron from angles nor common global lengths, complete face gluing or same-manifold realization follows from this scalar estimate.

An unequal-transverse direct-angle application uses the original six-position vector (r,a,b,o,a,b), with r,a,b,o>1, and assumes all six raw cosine values lie strictly between -1 and 1. Let theta, beta and delta be their principal arccos values at positions 0, 1 and 2. If r>=1+a+b, then pi<2theta+beta+delta. The parameters have no upper bound, a and b need not coincide, and equality in the length threshold is included. The mixed-coordinate comparison on [1,2] is not used for this application.

Put k=a+b, j=a-b, Dr=rad(r,a,b), Do=rad(o,a,b), L=k^2-(r-1)(o-1) and M=(r+1)(o+1)-j^2. At position 0 the raw numerator is N=2ab+r(a^2+b^2)-(r^2-1)o. At positions 1 and 2 the numerators are Na=b(r+o)+a(ro+b^2-a^2+1) and Nb=a(r+o)+b(ro+a^2-b^2+1), with common denominator sqrt(Dr Do). Expanding the original formula gives Dr(1+cos(theta))=(r+1)L and Dr(1-cos(theta))=(r-1)M, so L,M>0. It also gives Dr Do-Na^2=(a^2-1)LM and Dr Do-Nb^2=(b^2-1)LM. Principal angles in (0,pi) have positive sine, hence sin(beta)=sqrt(a^2-1)sqrt(LM)/sqrt(Dr Do) and the analogous identity for delta.

Write S=sqrt(a^2-1)+sqrt(b^2-1), T=(r-1)M/((r+1)L), Q=S^2(r-1)/((r+1)k^2), and F(z)=(z-1)(2(z+1)-j^2)/((z+1)k^2). Positive transverse lengths give S^2>k(k-2) and j^2<(k-2)^2. Since r>=k+1, Q>(k-2)/(k+2). The exact remainder T-F(r)=2(r-1)(o-1)Dr/((r+1)Lk^2) is strictly positive, even when F(r) is negative. Furthermore F(r)-F(k+1)=2(r-k-1)((r+1)(k+2)-j^2)/((r+1)(k+2)k^2)>=0 and F(k+1)>(6-k)/(k+2). Thus T+2Q>1 on the entire stated domain, including r=k+1.

Let eta=(beta+delta)/2 and d=(beta-delta)/2. Principal-angle bounds give 0<eta<pi and |d|<pi/2. The sum-to-product identities, cos(beta)+cos(delta)=kM/sqrt(Dr Do), and the positive-sine formulas give sin(eta)kM=cos(eta)S sqrt(LM). Squaring and using sin(eta)^2+cos(eta)^2=1 yields cos(eta)^2=k^2 M/(k^2 M+S^2 L). The inequality T+2Q>1 implies cos(eta)^2<1-cos(theta). If theta<pi/2, then 0<cos(theta)<1, so cos(eta)^2<sin(theta)^2. Since sin(theta)>0, cos(eta)<sin(theta); this conclusion also covers negative cos(eta). Cosine decreases on [0,pi], giving eta>pi/2-theta. If theta>=pi/2, the positive transverse angles give the desired inequality directly. These two branches establish pi<2theta+beta+delta without an acute-angle premise.

This application concerns the same raw numerator, radicands and actual six-position framing as the existing formula. Identifying its principal angles with those of an actual genuine tetrahedron remains a separate angle-length requirement. It supplies neither a common zero-curvature global length vector, distinct tetrahedra along an actual edge star, a global transverse-angle budget nor a geometric realization of the original manifold. The square-root, rational-order and trigonometric results are reused, and no literature priority is asserted.

**Theorem 1.1 (Increasing neighbours and decreasing the opposite coordinate).**

$$\forall x \in \mathrm{Real}, y \in \mathrm{Real}, z \in \mathrm{Real}, o \in \mathrm{Real}, v \in \mathrm{Real}, w \in \mathrm{Real}, Y \in \mathrm{Real}, Z \in \mathrm{Real}, O \in \mathrm{Real}, V \in \mathrm{Real}, W \in \mathrm{Real},\; \left(x \in Icc\left(1, 2\right) \land \left(y \in Icc\left(1, 2\right) \land \left(z \in Icc\left(1, 2\right) \land \left(o \in Icc\left(1, 2\right) \land \left(v \in Icc\left(1, 2\right) \land \left(w \in Icc\left(1, 2\right) \land \left(Y \in Icc\left(1, 2\right) \land \left(Z \in Icc\left(1, 2\right) \land \left(O \in Icc\left(1, 2\right) \land \left(V \in Icc\left(1, 2\right) \land \left(W \in Icc\left(1, 2\right) \land \left(y \le Y \land \left(z \le Z \land \left(O \le o \land \left(v \le V \land w \le W\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow cosine\left(x, y, z, o, v, w\right) \le cosine\left(x, Y, Z, O, V, W\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FourCycleEnvelopes.cosine_mixed_comparison` (`✓ std3`). ∎

*Citation.* Xinrong Zhao (2026). *Combinatorial Ricci Flows and Hyperbolic Structures on a Class of Compact 3-Manifolds with Boundary*. DOI: [10.48550/arXiv.2601.15174](https://doi.org/10.48550/arXiv.2601.15174). URL: <https://arxiv.org/html/2601.15174v2>.

*Commentary.*

All eleven variables lie in [1,2]. Increasing the four neighbouring coordinates and decreasing the opposite coordinate cannot decrease the actual cosine. The proof differentiates the original square-root expression and derives the nonnegative coupled numerator (x^2-1)(xow+xv+yo+yvw+z(1-w^2)). It retains endpoint continuity, positive denominators and the two actual tetrahedral symmetries.

Endpoint envelopes used by later incidence arguments are obtained there by direct specialization and normalization. They are not separate formal declarations. Geometric identification with a tetrahedron, face-pairing topology and the global co-volume existence argument remain outside this analytic theorem.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FourCycleEnvelopes.cosine_mixed_comparison`
