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

Injectivity follows directly from the dyadic coordinates. If j(t)=0, choose n with 2^n greater than the absolute value of t. Coordinate n says that t/2^n is an integer. Its absolute value is less than one, so it is zero and hence t=0. The additive kernel criterion makes j injective; cancellation supplies uniqueness of t. The local coordinate induction and kernel argument are consumed helpers, while the new construction is the identification of arbitrary dyadic paths.

Let h be the parent's alternating order-three point thirdPoint. If a path joined zero to h, the classification would give h=j(t). Then r maps to j(t r) would be a continuous additive real homomorphism taking 1 to h, contradicting the parent's real-time obstruction. Consequently S2 is connected but is not path connected. The parent's algebraic rational homomorphism taking 1 to h is discontinuous and does not supply a path or a continuous real action through h.

The proof reuses the pinned Mathlib covering, path-lifting, unbounded-power and additive-circle APIs and the repository's dyadic construction. The covering technique also occurs in StreamlineDecomposition for the different all-degree carrier. These are classical solenoid phenomena; no literature novelty or physical realization is asserted.

## References

- Truth anchor: `D5/S1/Solenoid/DyadicPathComponent.dyadic_path_orbit_classification`
- Dependency: [D5/S1/Solenoid/DyadicTimeSeparation](DyadicTimeSeparation.md)
