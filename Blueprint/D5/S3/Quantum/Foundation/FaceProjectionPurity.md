# Least confirmation and face projection purity

## Abstract

Least confirmation in the full original effect interval forces positive orthogonal face projections to preserve pure rays.

Let A be a finite dimensional real normed vector space. C is the original closed PointedCone, u is the original real linear unit, and u(x)>0 for every nonzero x in C. Assume that C contains a nonzero vector. Write K=base(C,u)={x in C : u(x)=1} and P=pure(C,u), the entire real extreme-point set of K. The norm gives the original finite dimensional topology; its numerical values are not identified with the pairing below. All effects are real linear functionals on this same A. proper(C,u,f) means 0<=f(x)<=u(x) for every x in C, and confirms(C,u,p,f) additionally means f(p)=1.

B is a real bilinear form on A, symmetric and positive definite: B(x,y)=B(y,x), and B(x,x)>0 for x!=0. Its self-duality is the exact equivalence x in C if and only if B(x,y)>=0 for every y in C. For every p in the entire original P, the functional B(p,-) is proper and confirms p. It is least among all original proper confirmers: for every real linear f confirming p and every x in C, B(p,x)<=f(x). There is no finite replacement of P or restriction of the effect interval.

F is any native PointedCone.Face of C. Q:A->A is real linear, idempotent on all of A, and B-self-adjoint: Q(Qx)=Qx and B(Qx,y)=B(x,Qy) for all x,y. Q sends every x in C into F and fixes every x in F. These are explicit positive orthogonal face-projection suppliers. No positivity of Id-Q, covering axiom, face-capacity bound, spectrality, Jordan product or filter-purity assumption is present. The zero face and full face are included.

**Theorem 1.1 (Every original pure input projects to zero or a pure ray).**

Lean statement: `D5/S3/Quantum/Foundation/FaceProjectionPurity.least_confirmation_face_purity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FaceProjectionPurity.least_confirmation_face_purity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every A,C,u,B,F,Q satisfying exactly the preceding hypotheses, P={x in K : B(x,x)=1}; P is compact and nonempty; and for every p in P either Qp=0 or all three of the following hold: u(Qp)>0, u(Qp)^(-1) Qp belongs to the original P, and Qp=u(Qp)[u(Qp)^(-1) Qp]. The normalization uses the original unit and original carrier. The nonzero-cone hypothesis supplies the pure maximizer. No division by u(Qp) is made until the nonzero-output branch.

The compactness of K and extension of linear inequalities from every original pure point to C are supplied by CircuitBalancedConfirmation.base_compact, nonneg_on_cone and cone_bound. Properness of B(p,-) gives B(p,x)<=u(x). Symmetry and pure-point extension therefore give B(x,y)<=u(x)u(y) for all x,y in C, in particular B(x,x)<=u(x)^2. A point x in K with B(x,x)=1 is extreme: in any strict convex decomposition, both supporting values B(x,y),B(x,z) must equal one; positive definiteness applied to y-x forces y=x. Conversely, confirmation gives B(p,p)=1 for each original pure p. Thus P is a closed level set in compact K. Krein-Milman and a nonzero cone vector give its nonemptiness.

Finite dimensional nondegeneracy of B makes the linear map x |-> B(x,-) bijective onto the real dual, so the proof constructs U with B(U,-)=u. Self-duality and the preceding bilinear bound give u(x)U-x in C. Set I(x)=u(x)^2-B(x,x), nonnegative on C and zero on P. Continuity in the original topology and compactness of the entire P give an actual pure maximizer p of I(Qr). Put d=I(Qp)>=0, z=Qp, a=u(z), and g=a QU-z. Positivity and idempotence give g=Q(aU-z) in F, while self-adjointness gives B(g,p)=d.

For every original pure r, consider v_r=(u(Qr),r-Qr) with the positive direct-sum form (a,x),(b,y) |-> ab+B(x,y). Orthogonality gives its squared length 1+I(Qr) and its pairing with v_p equal to B(p+g,r). Cauchy-Schwarz and maximality give B(p+g,r)^2<=(1+d)(1+I(Qr))<=(1+d)^2. Since p+g is in C, self-duality makes this value nonnegative. Hence 0<=B(p+g,r)<=1+d for every original pure r, with equality at p. The squared Cauchy-Schwarz calculation is equivalent to the square-root bound and introduces no norm-compatibility premise.

Consequently f=B(p+g,-)/(1+d) is in the entire original proper interval by cone_bound and satisfies f(p)=1. Full leastness gives B(p,x)<=f(x) for every x in C. Multiplication by the strictly positive 1+d and self-duality then give g-dp in C. If d>0, the positive decomposition g=dp+(g-dp) and g in the original face F force p in F. The fixing property gives Qp=p and therefore d=I(p)=0, a contradiction. Thus d=0, every I(Qr)=0, and in the nonzero-output branch the proved pure-locus characterization gives the stated original normalization.

This is the conditional maximum argument recorded in Library/QuantumStates/mullerududec2012selfduality.md, under Least confirmation forces face-filter purity. The impurity expression also occurs in Barnum-Muller-Ududec, arXiv:1403.4147v4, Definition 27; no literature priority is asserted. The theorem removes a separate purity premise once the represented full least effects, self-dual positive definite pairing and positive orthogonal face projections are supplied. It does not construct those suppliers from Principle S, assemble an S-to-Jordan classification, identify physical preparations, or supply composite and dynamical interfaces.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FaceProjectionPurity.least_confirmation_face_purity`
- Dependency: [D5/S3/Quantum/Foundation/CircuitBalancedConfirmation](CircuitBalancedConfirmation.md)
