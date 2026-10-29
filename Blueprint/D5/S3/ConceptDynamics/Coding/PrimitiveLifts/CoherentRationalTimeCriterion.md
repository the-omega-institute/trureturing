# The full coherent rational-time criterion

## Abstract

A coherent rational action on an arbitrary return-atlas family exists exactly when its finite actual isotypic classes have period one and coherently extensible holonomy.

The universes u, v and w are independent. H:Type u is any group, iota:Type w is any index type, X:iota->Type v is a dependent family, and A_i:ReturnAtlas H (X i) is a complete signed return chart for each actual index i. The family may be empty, and finite and infinite isotypic classes may coexist. No commutativity, common exponent, nilpotence or holonomy-centrality hypothesis is imposed on H.

Each chart has a positive natural period d_i and holonomy h_i. Its points point(t,z), for t:Int and z:H, cover X i and satisfy point(t,z)=point(s,w) exactly when t=s+d_i*m and z*h_i^m=w for an integer m. Time advances t by one; deck(a) multiplies z on the left. On the dependent disjoint union Sigma X these give T=jointTime A and D_a=jointDeck A a. Isotypic A i j means d_i=d_j and b*h_j=h_i*b for some b:H. IsotypicClass(A,i) is the actual subtype {j:iota | Isotypic A i j}, including every occurrence of an isotypic chart; it is not the quotient of types.

**Theorem 1.1 (One action, with an exact necessary and sufficient condition).**

$$\forall u \in Universe, v \in Universe, w \in Universe, H \in \operatorname{TypeAt}\left(u\right),\; [\operatorname{Group}\left(H\right)]\forall iota \in \operatorname{TypeAt}\left(w\right), X \in \operatorname{Map}\left(iota, \operatorname{TypeAt}\left(v\right)\right), A \in \operatorname{DependentReturnAtlases}\left(H, X\right),\; (\exists rho \in \operatorname{MonoidHom}\left(\operatorname{Multiplicative}\left(Rational\right), \operatorname{Perm}\left(\operatorname{Sigma}\left(X\right)\right)\right),\; ((\forall q \in \operatorname{Multiplicative}\left(Rational\right), a \in H, x \in \operatorname{Sigma}\left(X\right),\; \operatorname{apply}\left(\operatorname{apply}\left(rho, q\right), \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), x\right)\right) = \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), \operatorname{apply}\left(\operatorname{apply}\left(rho, q\right), x\right)\right)) \land (\operatorname{underlyingFunction}\left(\operatorname{apply}\left(rho, \operatorname{ofAdd}\left(1\right)\right)\right) = \operatorname{jointTime}\left(A\right)))) \iff (\forall i \in iota,\; \operatorname{Finite}\left(\operatorname{IsotypicClass}\left(A, i\right)\right) \implies ((\operatorname{period}\left(\operatorname{apply}\left(A, i\right)\right) = 1) \land (\exists phi \in \operatorname{MonoidHom}\left(\operatorname{Multiplicative}\left(Rational\right), H\right),\; \operatorname{apply}\left(phi, \operatorname{ofAdd}\left(1\right)\right) = \operatorname{holonomy}\left(\operatorname{apply}\left(A, i\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/CoherentRationalTimeCriterion.coherent_rational_time_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplicative Rational is the additive rational group written multiplicatively. Its identity is ofAdd(0), whereas ofAdd(1) is unit time. The existential quantifier chooses one monoid homomorphism rho into the permutation group of the entire Sigma X. Every rho(q) commutes with every specified D_a, and equality at unit time is equality of underlying functions on the whole carrier. The right side constrains precisely the finite actual classes: for every such i, d_i=1 and there exists a genuine homomorphism phi:Multiplicative Rational ->* H with phi(ofAdd(1))=h_i. No condition on period or holonomy is imposed on infinite actual classes.

For necessity, the homomorphism law and commutativity of the rational source imply that every rho(q) commutes with T=rho(ofAdd(1)). PrimeOrbitRootCriterion.component_constant then makes the first component of rho(q)(i,x) independent of x. Evaluating it at point(0,1) defines an action sigma on the actual index set. The identity and multiplication laws follow from those of rho and this component constancy. PrimeOrbitRootCriterion.routing_isotypic shows that sigma preserves the actual isotypic classes, using the injectivity of the permutation rho(q).

Fix a finite actual class C_i and restrict the index action to it. A group-source homomorphism into endomorphisms gives genuine permutations via toHomPerm. For any homomorphism f from Multiplicative Rational to a finite group K, put N=Nat.card K>0. The identity q=(ofAdd(toAdd(q)/N))^N and Mathlib's pow_card_eq_one' imply f(q)=1. Apply this to the permutation group of C_i. Every rational time therefore fixes i. Restrict rho to the subtype of Sigma X with first component i, transport through Equiv.sigmaSubtype i, and obtain one genuine rational permutation homomorphism on X i. RationalReturnAtlasCriterion.rational_time_action_criterion now gives exactly d_i=1 and the coherent holonomy homomorphism into H, including when H is noncommutative.

For sufficiency, let F(i) mean that the actual class C_i is finite. Isotypy identifies actual classes by the equivalence that keeps their indices, so F is invariant under isotypy. On the subfamily {i | F(i)}, the single-chart criterion supplies a rational action on each X i; their dependent disjoint union is a rational permutation homomorphism. On the complementary subfamily {i | not F(i)}, its restricted actual class is equivalent to the original class: all members of that class also fail F. It is therefore infinite. Apply RationalTimeAction.exists_rational_time_action once to this complementary subfamily, with no holonomy restriction.

Finally, Equiv.subtypeSigmaEquiv and Equiv.sumCompl identify Sigma X with the binary sum of these two dependent subfamilies. Equiv.Perm.sumCongrHom combines their rational actions, and conjugation through this partition equivalence gives the required action on the original carrier. The partition equivalence intertwines the specified deck maps and time, so these equalities hold on the entire original family, including either empty part. The identity, negative-time, addition and denominator-compatibility laws all come from the genuine monoid homomorphisms.

UniversalRootCriterion concerns a weaker requirement: a separately chosen root for every positive degree, with no compatibility among choices. Such independent root existentials do not supply the coherent homomorphisms used here. The present proof uses the existing all-infinite construction and single-chart criterion and supplies the missing finite-class routing, restriction and mixed-family assembly. This is an algebraic criterion, with classical choice permitted; it makes no literature-priority, continuity, real-time extension or physical-realization claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/CoherentRationalTimeCriterion.coherent_rational_time_iff`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalReturnAtlasCriterion](RationalReturnAtlasCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalTimeAction](RationalTimeAction.md)
