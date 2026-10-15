# Original native signed time normal forms

## Abstract

The full integral unit classification acts on every original native centralizer automorphism and every original full-rho value.

Native(q) is literally DimensionGroup(resetMatrix q), Theta is actual forward resetTheta q, and Phi=nativeIntEquiv q hq is the existing integer-linear cyclic chart. nativeGluing is Phi inverse followed by the new integral gluing. Only an integer-linear equivalence is asserted on Native; no multiplication or ring structure is assigned to that original group.

**Theorem 1.1 (The literal original native orientation).**

$$\forall q \in Nat, hq \in \operatorname{positive}\left(q\right),\; \left(\forall z \in \operatorname{QF}\left(q\right),\; \operatorname{nativeGluing}\left(q, hq, \operatorname{nativeIntEquiv}\left(q, hq, z\right)\right) = \operatorname{gluing}\left(q, z\right)\right) \land \left(\left(\forall v \in \operatorname{Native}\left(q\right),\; \operatorname{nativeGluing}\left(q, hq, \operatorname{resetTheta}\left(q, v\right)\right) = \operatorname{multiply}\left(\operatorname{gluing}\left(q, \operatorname{fp}\left(q, X\right)\right), \operatorname{nativeGluing}\left(q, hq, v\right)\right)\right) \land \left(\left(\forall v \in \operatorname{Native}\left(q\right),\; \operatorname{nativeGluing}\left(q, hq, \operatorname{groupAction}\left(\operatorname{resetMatrix}\left(q\right), \operatorname{ofAdd}\left(true\right), v\right)\right) = \operatorname{multiply}\left(\operatorname{gluing}\left(q, \operatorname{fp}\left(q, \operatorname{W}\left(q\right)\right)\right), \operatorname{nativeGluing}\left(q, hq, v\right)\right)\right) \land \left(\left(\forall z \in Int, v \in \operatorname{Native}\left(q\right),\; \operatorname{nativeGluing}\left(q, hq, \operatorname{integerScale}\left(z, v\right)\right) = \operatorname{integerScale}\left(z, \operatorname{nativeGluing}\left(q, hq, v\right)\right)\right) \land \left(\forall n \in Nat, v \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{nativeGluing}\left(q, hq, \operatorname{nativeStage}\left(q, n, v\right)\right) = \operatorname{gluing}\left(q, \operatorname{ringEquiv}\left(q, \operatorname{pp}\left(q, \operatorname{coordinatePolynomial}\left(resetLabel, q, \operatorname{apply}\left(\operatorname{power}\left(\operatorname{resetInverse}\left(q, hq\right), n\right), v\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm.native_gluing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

positive(q) is 0<q. Time acts by the compatible pair ([X],[X]); the actual original Sign action acts by ([W],[W])=(1,-1). Scalars are the actual integer module action. For an original stage-n row, resetInverse^n acts BEFORE coordinatePolynomial; these inverse transition powers coexist with forward time X. The proof reuses all corresponding clauses of native_presentation, including its actual coefficient law.

**Definition 1.2 (A genuine unit from an actual commuting equivalence).**

$$\forall q \in Nat, hq \in \operatorname{positive}\left(q\right), A \in \operatorname{IntLinearEquiv}\left(\operatorname{Native}\left(q\right), \operatorname{Native}\left(q\right)\right), ht \in \operatorname{commutesWithForwardTime}\left(q, A\right),\; \operatorname{hasType}\left(\operatorname{scalarUnit}\left(q, hq, A, ht\right), \operatorname{Units}\left(\operatorname{QF}\left(q\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm.scalarUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

commutesWithForwardTime(q,A) means forall v, A(Theta(v))=Theta(A(v)). The owning ResetHistoryKernel.centralizingMap_scalar argument makes Phi inverse A Phi multiplication by its value at one. A inverse also commutes; its scalar supplies the actual inverse unit. nativeAction conjugates multiplication by this unit through Phi, and recovers the given A on every vector. This is the already documented cyclic scalar argument, retained as a consumed helper.

**Theorem 1.3 (Every native centralizer and every original rho value).**

$$\left(\forall A \in \operatorname{IntLinearEquiv}\left(N, N\right),\; \operatorname{commutesWithForwardTime}\left(2, A\right) \Rightarrow \left(\exists p \in \operatorname{product}\left(Int, \operatorname{product}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)\right),\; \left(\forall v \in N,\; \operatorname{apply}\left(A, v\right) = \operatorname{integerScale}\left(\operatorname{power}\left(\operatorname{neg}\left(1\right), \operatorname{val}\left(\operatorname{fst}\left(\operatorname{snd}\left(p\right)\right)\right)\right), \operatorname{apply}\left(\operatorname{power}\left(U, \operatorname{val}\left(\operatorname{snd}\left(\operatorname{snd}\left(p\right)\right)\right)\right), \operatorname{apply}\left(\operatorname{integerPower}\left(T, \operatorname{fst}\left(p\right)\right), v\right)\right)\right)\right) \land \left(\forall r \in \operatorname{product}\left(Int, \operatorname{product}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)\right),\; \left(\forall v \in N,\; \operatorname{apply}\left(A, v\right) = \operatorname{integerScale}\left(\operatorname{power}\left(\operatorname{neg}\left(1\right), \operatorname{val}\left(\operatorname{fst}\left(\operatorname{snd}\left(r\right)\right)\right)\right), \operatorname{apply}\left(\operatorname{power}\left(U, \operatorname{val}\left(\operatorname{snd}\left(\operatorname{snd}\left(r\right)\right)\right)\right), \operatorname{apply}\left(\operatorname{integerPower}\left(T, \operatorname{fst}\left(r\right)\right), v\right)\right)\right)\right) \Rightarrow r = p\right)\right)\right) \land \left(\forall h \in \operatorname{ResetFullAut}\left(2\right),\; \exists p \in \operatorname{product}\left(Int, \operatorname{product}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)\right),\; \left(\forall v \in N,\; \operatorname{apply}\left(\operatorname{rho}\left(2, positiveTwo, h\right), v\right) = \operatorname{integerScale}\left(\operatorname{power}\left(\operatorname{neg}\left(1\right), \operatorname{val}\left(\operatorname{fst}\left(\operatorname{snd}\left(p\right)\right)\right)\right), \operatorname{apply}\left(\operatorname{power}\left(U, \operatorname{val}\left(\operatorname{snd}\left(\operatorname{snd}\left(p\right)\right)\right)\right), \operatorname{apply}\left(\operatorname{integerPower}\left(T, \operatorname{fst}\left(p\right)\right), v\right)\right)\right)\right) \land \left(\forall r \in \operatorname{product}\left(Int, \operatorname{product}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)\right),\; \left(\forall v \in N,\; \operatorname{apply}\left(\operatorname{rho}\left(2, positiveTwo, h\right), v\right) = \operatorname{integerScale}\left(\operatorname{power}\left(\operatorname{neg}\left(1\right), \operatorname{val}\left(\operatorname{fst}\left(\operatorname{snd}\left(r\right)\right)\right)\right), \operatorname{apply}\left(\operatorname{power}\left(U, \operatorname{val}\left(\operatorname{snd}\left(\operatorname{snd}\left(r\right)\right)\right)\right), \operatorname{apply}\left(\operatorname{integerPower}\left(T, \operatorname{fst}\left(r\right)\right), v\right)\right)\right)\right) \Rightarrow r = p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm.native_normal_forms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here N=Native(2), positiveTwo is the proof 0<2, T is EXACTLY rho(2,positiveTwo,unitShift(ResetGraph 2)), and U is EXACTLY groupAction(resetMatrix 2)(ofAdd true), kept as an integer-linear endomorphism. The action in the formula is (-1)^a.val times U^b.val applied to T^n(v), for p=(n,a,b):Int times Fin 2 times Fin 2. Every commuting A is obtained from scalarUnit and the complete unit_normal_form; evaluation at the original cyclic generator reflects uniqueness through the injective unit action. rho_time uses literal membership of h in the original fullAutSubgroup and rho_unitShift, so the second clause covers EVERY original h without an extra Sign-equivariance, inertness, positivity or marker premise.

This is a repository synthesis; the integral reconstruction and coupled-unit classification supply the missing live content. The prior centralizer/scalar argument and native chart are reused at their owners. No literature novelty is claimed. The theorem bounds the actual rho image but does not prove that image is the whole ambient centralizer or exclude scalar minus sign. Such exclusion requires an additional original-beam positivity theorem and remains open. Uniform eigenlattices, conductor, additive cokernel and common-residue action consequences remain subsequent selected-package obligations.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm.native_gluing`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm.native_normal_forms`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm.scalarUnit`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetHistoryKernel](ResetHistoryKernel.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetIntegralUnits](ResetIntegralUnits.md)
