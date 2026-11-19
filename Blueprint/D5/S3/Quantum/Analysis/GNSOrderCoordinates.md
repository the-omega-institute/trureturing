# Positive commutant coordinates from GNS comparison

## Abstract

Classical order-Radon--Nikodym coordinates in the actual completed GNS of a positive functional on an arbitrary unital complex C-star algebra.

Let A be a unital complex C-star algebra with a compatible star order. The positive complex-linear functional psi is arbitrary: it need not be faithful, normalized or nonzero. Its GNS Hilbert space, representation pi and pre-GNS maps are the ones constructed by Mathlib. Omega is the image of the unit, without normalization. No separability, finite-dimensionality or countability assumption is used.

**Theorem 1.1 (The canonical comparison contraction).**

Lean statement: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.comparison_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSOrderCoordinates.comparison_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive complex-linear functionals phi and psi, suppose phi(a)<=psi(a) for every positive a. Sending psi.toPreGNS(a) to phi.toPreGNS(a) is complex linear and decreases the pre-GNS seminorm, since the squared norms are phi(a* a) and psi(a* a). Completing this map gives J: GNS(psi) to GNS(phi) with operator norm at most one. Completion accounts for null vectors, including the zero Hilbert space.

**Theorem 1.2 (Intertwining the actual representations).**

Lean statement: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.comparison_intertwines`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSOrderCoordinates.comparison_intertwines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a in A, J pi_psi(a)=pi_phi(a) J. This equality holds first on each pre-GNS vector by associativity of left multiplication and then on the whole completion by density and continuity. The image under J of the unnormalized cyclic vector for psi is the cyclic vector for phi.

**Theorem 1.3 (Adjoint intertwining).**

Lean statement: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.comparison_adjoint_intertwines`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSOrderCoordinates.comparison_adjoint_intertwines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking adjoints of the intertwining identity at a* gives J* pi_phi(a)=pi_psi(a) J*. Both representations are the actual star homomorphisms supplied by the completed GNS construction.

**Theorem 1.4 (A constructed positive commutant contraction).**

Lean statement: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coordinate_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coordinate_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set T=J*J. Then 0<=T<=I in the usual Loewner order on bounded Hilbert-space operators, and T commutes with pi_psi(a) for every a in A. Positivity is the adjoint-square theorem; the upper bound follows from the contraction estimate on all vectors; commutation follows from both intertwining identities.

**Theorem 1.5 (Exact coefficient of the original functional).**

Lean statement: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coordinate_represents`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coordinate_represents` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a in A, phi(a)=<Omega,T pi_psi(a) Omega>. More generally the coefficient between the pre-GNS images of a and b is phi(a* b). Thus T represents the given functional itself, including every singular input allowed by domination.

**Theorem 1.6 (Uniqueness on the full commutant).**

Lean statement: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coefficient_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coefficient_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two bounded operators T and S commuting with pi_psi(A), equality of their complex-linear coefficient functionals implies T=S. Neither operator needs to be positive or self-adjoint. Apply the existing cyclic Schur lemma to T-S and scalar zero, using the actual dense GNS orbit. That library theorem proves uniqueness by off-diagonal matrix coefficients and density.

**Theorem 1.7 (Positivity reflects through the cyclic coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coefficient_nonneg_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coefficient_nonneg_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any bounded commutant operator T, the coefficient is nonnegative on all positive elements of A if and only if T is positive in the Loewner order. In the reverse direction its quadratic form is nonnegative on the dense pre-GNS range, hence everywhere by continuity. The complex polarization criterion supplies self-adjointness; it is not assumed separately.

**Theorem 1.8 (Preservation and reflection of order).**

Lean statement: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coefficient_order_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coefficient_order_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary bounded commutant operators T and S, coefficient_T(a)<=coefficient_S(a) for every positive a if and only if T<=S. Apply positivity reflection to S-T. This is the actual positive-cone order on functionals and the usual operator order, with no change of order relation.

**Theorem 1.9 (The actual order-Radon--Nikodym existence theorem).**

Lean statement: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.existsUnique_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSOrderCoordinates.existsUnique_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive complex-linear phi dominated by psi on the positive cone has exactly one bounded operator T such that 0<=T<=I, T commutes with every pi_psi(a), and its coefficient functional is exactly phi. Existence uses the canonical J*J construction; uniqueness uses density. Conversely any positive commutant contraction defines a positive complex-linear functional dominated by psi by the same coefficient formula.

**Definition 1.10 (The constructed order isomorphism).**

Lean statement: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.orderCoordinates`

*Formalization.* `D5/S3/Quantum/Analysis/GNSOrderCoordinates.orderCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

DominatedFunctional(psi) is the subtype of Mathlib positive complex-linear functionals dominated by psi on positive elements. CommutantInterval(psi) is the subtype of bounded operators satisfying 0<=T<=I and commuting with every pi_psi(a). The map orderCoordinates is an actual order isomorphism between these two types: its forward map is J*J, its inverse is the coefficient functional, both composites are identities, and order comparison agrees in both directions. Antisymmetry of functional order uses the fact that positive elements span the complex C-star algebra.

**Theorem 1.11 (Coordinates for the original prescribed positive dual inputs).**

Lean statement: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.original_pair_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GNSOrderCoordinates.original_pair_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho and sigma be arbitrary continuous complex-linear functionals nonnegative on positive elements. Convert rho+sigma to its actual positive-linear-map GNS input without changing any value. There exists exactly one positive commutant contraction C whose coefficient is rho and whose complementary operator I-C has coefficient sigma, as equalities of complex-linear functionals. This includes singular rho and sigma, the zero input pair and nonnormalized masses. No normality assumption is needed for this more general existence statement.

For an order-normal psi, the existing NormalFunctionals.isOrderNormal_of_domination theorem applies directly to the inverse order coordinate, using 0<=eta_T<=psi. Its conclusion uses precisely the arbitrary-directed order-normality predicate; it does not identify order-normality with an independently defined coefficient-series predual.

These are classical foundational operator-algebra results, expressed using Mathlib's actual GNS spaces and completion API. The continuous coefficient functional, its evaluation on a* a, and the cyclic Schur lemma are reused from the Physicslib4 suppliers in IrreducibleBoundedLift. They supply order coordinates for the pending arbitrary-von-Neumann full-curvature maximal-hockey versus maximal-f classification. They do not establish normality of the GNS representation, the compressed centralizer criterion, full-curvature necessity, or realization of all reverse tests on the entire complex L1 space. In particular the required centralization concerns the open spectral corner PNP and cannot be replaced by global commutation.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coefficient_injective`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coefficient_nonneg_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coefficient_order_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.comparison_adjoint_intertwines`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.comparison_intertwines`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.comparison_norm_le`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coordinate_mem`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.coordinate_represents`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.existsUnique_coordinate`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.orderCoordinates`
- Truth anchor: `D5/S3/Quantum/Analysis/GNSOrderCoordinates.original_pair_coordinate`
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift](../Algebra/StateApproximation/IrreducibleBoundedLift.md)
