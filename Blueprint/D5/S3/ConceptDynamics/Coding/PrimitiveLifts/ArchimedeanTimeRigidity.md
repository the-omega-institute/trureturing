# Archimedean time rigidity

## Abstract

A nonzero continuous homomorphism from Archimedean field time into a group without p-torsion is injective.

Let K be an Archimedean linearly ordered field equipped with its order topology. Let A be an arbitrary additive group with a T1 topology, in a universe independent of K. In the formula, ArchimedeanOrderedFieldWithOrderTopology and TOneAddGroup abbreviate exactly these assumptions. The group A may be noncommutative, and continuity of its group operations is not assumed.

**Theorem 1.1 (Injectivity or triviality).**

$$\forall K \in ArchimedeanOrderedFieldWithOrderTopology, A \in TOneAddGroup, p \in Nat, f \in \operatorname{AddHom}\left(K, A\right),\; ((1 < p) \land ((\forall x \in A,\; (\operatorname{nsmul}\left(p, x\right) = 0) \implies (x = 0)) \land (\operatorname{Continuous}\left(f\right)))) \implies (\operatorname{Injective}\left(f\right) \lor f = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ArchimedeanTimeRigidity.continuous_addHom_injective_or_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a natural number p greater than one. Assume that p*x=0 implies x=0 for every x in A, where p*x denotes repeated addition. Every continuous additive homomorphism f:K->A is injective or is the zero homomorphism. The condition concerns only the fiber over zero; it does not assume injectivity of the entire p-fold multiplication map. No primality or absence of torsion at other integers is required.

Put S=ker(f). If S is the zero subgroup, f is injective. Otherwise, suppose a were its least positive element. The element b=a/p satisfies 0<b<a and p*b=a. Additivity gives p*f(b)=f(a)=0, so the target hypothesis gives f(b)=0. Thus b also belongs to S, contradicting leastness. The Archimedean subgroup density theorem now makes S dense. The set S is closed because it is the inverse image of the closed singleton {0} under the continuous map f. A closed dense subgroup is the whole field, hence f=0.

Both the rational field with its usual topology and the real field satisfy the source assumptions. Consequently a nontrivial continuous time homomorphism from either field into such a target cannot have a nonzero period: f(t)=0 forces t=0. A period in the sense f(s+t)=f(s) gives f(t)=0 by additivity and cancellation. This is injectivity, with no assertion that the map is a topological embedding or that its image is closed.

For a multiplicative group H, use A=Additive(H) with its supplied topology. The target assumption becomes x^p=1 implies x=1, and the zero homomorphism becomes the constant identity homomorphism. This is a change of notation and does not impose commutativity or a global unique-root property. The argument combines standard subgroup density and closedness results with the division-closed kernel observation; no literature priority or physical realization claim is made.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ArchimedeanTimeRigidity.continuous_addHom_injective_or_eq_zero`
