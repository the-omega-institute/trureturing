# Dyadic Solenoid Path Components and Unique Time

## Abstract

Two points of the actual dyadic solenoid are joined exactly when a unique real-flow time translates one to the other.

S2 is the existing DyadicSolenoid: compatible sequences of unit additive-circle coordinates with 2 x(n+1)=x(n), with the inherited product subspace topology. The actual additive map j=realFlow has coordinate j(t)(n)=t/2^n modulo one. This is the doubling inverse limit, distinct from the all-positive-degree UniversalSolenoid; no change of carrier or topology is made.

**Theorem 1.1 (A unique real translation characterizes being joined).**

$$\forall x, y \in S2,\ \operatorname{Joined}(x, y) \iff \exists! t \in \mathbb{R},\ y = j(t) + x$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/DyadicPathComponent.dyadic_path_orbit_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x and y in S2, Joined x y holds if and only if there is exactly one real t with y=j(t)+x. Thus the real translation action is free and its orbits are precisely the path components. Uniqueness concerns the endpoint time, not the parametrization of the path.

Translate a path from x to y by subtracting x. Lift its zeroth circle coordinate through the covering from the real line to the unit circle, with initial lift zero. Write the continuous real lift as a. Dyadic compatibility gives 2^n times coordinate n equal to coordinate zero. Both coordinate n of the translated path and the circle class of a/2^n lift that same coordinate-zero path through multiplication by 2^n. They agree initially, so covering-lift uniqueness on the connected unit interval identifies them everywhere. The endpoint is j(a(1)). Conversely u maps to j(u t)+x along the unit interval and is an explicit path.

The independent repository theorem continuous_addHom_injective_or_eq_zero in ArchimedeanTimeRigidity is applied with K=R, A=S2 and p=2. The public dyadic_time_separation package supplies continuity of j and the zero kernel of doubling. The circle coordinate j(1/2)(0)=[1/2] is nonzero, ruling out the zero homomorphism. Hence j is injective; cancellation supplies uniqueness of t. The local coordinate induction and rigidity application are consumed helpers, while the new construction is the identification of arbitrary dyadic paths.

Let h be the parent's alternating order-three point thirdPoint. If a path joined zero to h, the classification would give h=j(t). Then r maps to j(t r) would be a continuous additive real homomorphism taking 1 to h, contradicting the parent's real-time obstruction. Consequently S2 is connected but is not path connected. The parent's algebraic rational homomorphism taking 1 to h is discontinuous and does not supply a path or a continuous real action through h.

The proof reuses the pinned Mathlib covering and path-lifting APIs and the repository's verified time rigidity and dyadic construction. The covering technique also occurs in StreamlineDecomposition for the different all-degree carrier. These are classical solenoid phenomena; no literature novelty or physical realization is asserted.

## References

- Truth anchor: `D5/S1/Solenoid/DyadicPathComponent.dyadic_path_orbit_classification`
- Dependency: [D5/S1/Solenoid/DyadicTimeSeparation](DyadicTimeSeparation.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ArchimedeanTimeRigidity](../../S3/ConceptDynamics/Coding/PrimitiveLifts/ArchimedeanTimeRigidity.md)
