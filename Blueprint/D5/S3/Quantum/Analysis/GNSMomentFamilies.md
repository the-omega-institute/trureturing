# Continuous moments in the GNS commutant

## Abstract

Full complex continuous moments and the actual completed GNS commutant.

Let A be an arbitrary unital complex C-star algebra with its compatible star order, and let rho and sigma be positive continuous complex-linear functionals. Put psi=rho+sigma. All operators below act on Mathlib's actual completed GNS Hilbert space of psi. Omega is the image of the unit, with no normalization. The commutant N is the norm-closed star subalgebra of operators commuting with the actual GNS representation of every a in A. The construction includes zero and singular input functionals and nonseparable Hilbert spaces. It does not require normality of the GNS representation.

**Definition 1.1 (The actual closed operator commutant).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.commutant`

*Formalization.* `D5/S3/Quantum/Analysis/GNSMomentFamilies.commutant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N is the star-subalgebra centralizer of the range of the completed GNS representation. Because that range is star closed, membership is exactly commutation with every represented element. Its carrier is closed, so N inherits the C-star norm, completeness and the usual operator order.

**Definition 1.2 (An injective complex-linear coefficient map).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap`

*Formalization.* `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For T in N define K(T)(a)=<Omega,T pi(a) Omega>. This is the existing continuous coefficient functional, now assembled as a complex-linear map from the actual commutant into the continuous dual of A. Its linearity follows from linearity of the inner product in the second argument.

**Theorem 1.3 (Coefficients determine commutant operators).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality K(T)=K(S) implies T=S, by the cyclic coefficient injectivity theorem. Both operators may be arbitrary complex commutant operators; positivity is unnecessary.

**Theorem 1.4 (The coefficient reflects positivity).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K(T) is nonnegative on every positive a in A if and only if T is positive in N. This is the positive coefficient reflection theorem for the actual dense cyclic orbit, with the inherited operator order.

**Theorem 1.5 (Coefficient order is exactly operator order).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_order`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary commutant operators T and S, K(T)(a)<=K(S)(a) on every positive a if and only if T<=S. This directly reuses the existing cyclic GNS order-reflection theorem and supplies both original overlap feasibility bounds.

**Theorem 1.6 (The unit has its original GNS coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of the identity is precisely psi. Evaluating at a gives the GNS inner product of the images of 1 and a, which equals psi(a), including when the GNS space is zero.

**Definition 1.7 (The actual unnormalized vector functional).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.vectorFunctional`

*Formalization.* `D5/S3/Quantum/Analysis/GNSMomentFamilies.vectorFunctional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Define phi(T)=K(T)(1)=<Omega,T Omega>. This is a positive complex-linear functional on N.

**Theorem 1.8 (Faithfulness on positive commutant operators).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.vectorFunctional_faithful`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSMomentFamilies.vectorFunctional_faithful` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If T is positive in N and phi(T)=0, then T=0. Indeed K(T) is a positive continuous functional on A. Its norm equals its real mass at the unit, hence it has norm zero. Injectivity of K then forces T=0. This proves positivity-faithfulness of the actual GNS vector functional on N without assuming faithfulness of psi on A.

**Definition 1.9 (The original positive GNS input).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.pairFunctional`

*Formalization.* `D5/S3/Quantum/Analysis/GNSMomentFamilies.pairFunctional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Convert the original continuous dual functional rho+sigma to a positive complex-linear map without changing any value.

**Definition 1.10 (The original first-moment operator).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.pairCoordinate`

*Formalization.* `D5/S3/Quantum/Analysis/GNSMomentFamilies.pairCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use rho<=psi to construct the GNS comparison contraction J, and set C=J*J in N. Thus 0<=C<=I, K(C)=rho and K(I-C)=sigma. No coordinate operator is supplied as a premise.

**Theorem 1.11 (Exact first-moment coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.pairCoordinate_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSMomentFamilies.pairCoordinate_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed C has coefficient rho on every complex input a in A, by the dominated GNS coordinate formula.

**Theorem 1.12 (Every full Family has an actual positive lift).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.exists_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSMomentFamilies.exists_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual NormalMomentFamily.Family F, let J_F be its complex-linear map on all complex continuous functions on [0,1]. A nonnegative g obeys 0<=J_F(g)<=(norm(g)+1) psi on positive algebra elements. Apply the dominated GNS coordinate theorem to J_F(g)/(norm(g)+1), then scale its coordinate, to put J_F(g) in the range of K. The C-star four-positive-part decomposition puts every J_F(g) in this same complex-linear range. Invert the injective linear coefficient map on its range and compose with J_F. The resulting actual positive complex-linear Z takes values in N, satisfies Z(1)=I and Z(u)=C, and K(Z(g))=J_F(g) for every complex continuous g. No norm-dependent choice is assumed linear; linearity comes from the range equivalence.

**Definition 1.13 (The converse with the prescribed first moment).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.familyOfMap`

*Formalization.* `D5/S3/Quantum/Analysis/GNSMomentFamilies.familyOfMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive complex-linear Z into N with Z(1)=I and Z(u)=C, compose K with Z and apply NormalMomentFamily.ofLinearMap. This constructs the full Family for the fixed original pair. The first-moment condition is essential: a positive unital map with another value at u describes another pair.

**Theorem 1.14 (Every complex coordinate is retained).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.familyOfMap_agrees`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSMomentFamilies.familyOfMap_agrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Family constructed from Z has J_F(g)=K(Z(g)) for every complex continuous g, by the actual definition of its continuous dual coordinates.

**Definition 1.15 (The full correspondence).**

Lean statement: `D5/S3/Quantum/Analysis/GNSMomentFamilies.familyEquiv`

*Formalization.* `D5/S3/Quantum/Analysis/GNSMomentFamilies.familyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is an actual equivalence between the full Family for rho and sigma and positive complex-linear maps Z into N with Z(1)=I and Z(u)=C. The forward and reverse constructions are inverse on every complex continuous function. Equality on the operator side follows from coefficient injectivity, while equality on the Family side is equality of all continuous dual coordinates.

These are classical GNS order and positive-map constructions. The domain is the whole complex continuous-function algebra, not a polynomial or simple-function restriction. Positive maps between the inherited ordered C-star algebras are automatically bounded. The correspondence alone asserts neither normality of the original GNS representation nor a compressed-centralizer classification.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_injective`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_nonneg`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_one`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.coefficientMap_order`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.commutant`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.exists_lift`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.familyEquiv`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.familyOfMap`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.familyOfMap_agrees`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.pairCoordinate`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.pairCoordinate_coefficient`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.pairFunctional`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.vectorFunctional`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSMomentFamilies.vectorFunctional_faithful`
- Dependency: [D5/S3/Quantum/Analysis/GNSOrderCoordinates](GNSOrderCoordinates.md)
- Dependency: [D5/S3/Quantum/Analysis/NormalMomentFamily](NormalMomentFamily.md)
- Dependency: [D5/S3/Quantum/Analysis/PositiveMomentRigidity](PositiveMomentRigidity.md)
