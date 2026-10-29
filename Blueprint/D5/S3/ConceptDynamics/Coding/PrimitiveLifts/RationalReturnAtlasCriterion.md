# Rational time on a single complete return chart

## Abstract

One complete return chart supports rational time precisely when its phase period is one and its holonomy extends to a rational group homomorphism.

**Theorem 1.1 (Exact criterion for a coherent rational action).**

$$\forall u \in Universe, v \in Universe,\; \forall H \in \operatorname{Type}\left(u\right),\; [\operatorname{Group}\left(H\right)]\forall X \in \operatorname{Type}\left(v\right), A \in \operatorname{ReturnAtlas}\left(H, X\right),\; ((\exists rho \in \operatorname{MonoidHom}\left(\operatorname{Multiplicative}\left(Rational\right), \operatorname{Perm}\left(X\right)\right),\; ((\forall q \in \operatorname{Multiplicative}\left(Rational\right),\; \operatorname{Equivariant}\left(A, \operatorname{apply}\left(rho, q\right)\right)) \land \operatorname{underlyingFunction}\left(\operatorname{apply}\left(rho, \operatorname{ofAdd}\left(1\right)\right)\right) = \operatorname{time}\left(A\right))) \iff (\operatorname{period}\left(A\right) = 1 \land \exists phi \in \operatorname{MonoidHom}\left(\operatorname{Multiplicative}\left(Rational\right), H\right),\; \operatorname{apply}\left(phi, \operatorname{ofAdd}\left(1\right)\right) = \operatorname{holonomy}\left(A\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalReturnAtlasCriterion.rational_time_action_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universes u and v are independent. H is any group, X is any carrier, and A is a complete signed ReturnAtlas H X. A has a positive natural period d, holonomy h in H, and coordinates point(t,z). Its complete equality relation is point(t,z)=point(s,w) exactly when t=s+d*m and z*h^m=w for some integer m. Its time map advances t by one, while deck(a) multiplies z on the left. These are the entire hypotheses; H may be infinite, noncommutative or have torsion.

Multiplicative Rational is the additive group of all rational numbers written multiplicatively. Its identity is ofAdd(0); ofAdd(1) is the positive unit time. A monoid homomorphism rho into Perm X is one coherent action, with rho(ofAdd(q+r))=rho(ofAdd(q))*rho(ofAdd(r)) and rho(ofAdd(0)) the identity permutation. Equivariant A (rho(q)) means that rho(q)(deck(a,x))=deck(a,rho(q)(x)) for every a in H and x in X. The displayed equality at unit time is equality of the underlying functions on all X. Neither continuity nor an order or topology is assumed.

For necessity, put R=rho(ofAdd(1/d)). The homomorphism law gives R^d=rho(ofAdd(1)), hence the dth iterate of R is A.time. Apply the existing ReturnAtlas.root_criterion at k=d. Its signed equation is d*s.val=1+d*m, so d divides 1 and d=1. This uses the existing signed root classification rather than a separate classification of roots.

When d=1, the existing complete atlas coordinates give the equivalence e:H equiv X defined by e(z)=point(0,z). The left deck law becomes e(a*z)=deck(a,e(z)); the signed return relation gives time(e(z))=e(z*h). Every deck-equivariant permutation rho(q) therefore has the form rho(q)(e(z))=e(z*b(q)), where b(q)=e inverse(rho(q)(e(1))). With permutation multiplication interpreted as composition, right translations satisfy R(b)*R(c)=R(c*b). Consequently the immediate composition rule is b(p*q)=b(q)*b(p). Commutativity of the rational source also gives b(p*q)=b(p)*b(q), producing the required genuine homomorphism phi into H. Unit time forces phi(ofAdd(1))=h.

Conversely, a homomorphism phi with this unit value defines rho(q) by transporting z maps to z*phi(q) through e. The images of phi commute because the rational source is commutative, so these right translations satisfy the permutation homomorphism law in its actual composition order. Associativity makes them commute with every left deck translation, and the value at ofAdd(1) is exactly time. The construction includes zero and negative rational times and uses neither finite nor countable carriers nor a divisibility hypothesis on H.

This is a repository derivation from the complete return chart and its existing root criterion. The result concerns a single specified chart and its specified deck action. It makes no literature priority claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalReturnAtlasCriterion.rational_time_action_criterion`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion](PrimitiveLiftRootCriterion.md)
