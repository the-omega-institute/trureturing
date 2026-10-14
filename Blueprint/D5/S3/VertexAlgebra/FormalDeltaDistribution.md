# FormalDeltaDistribution

## Abstract

Three-variable formal delta: FormalDeltaDistribution

These declarations retain the accepted three-variable formal-delta construction. Canonical transport supplies no new mathematical credit. Declaration handles bind to compiled source; WithoutFormula does not display a formula or replace the full Lean statement and proof.

The three independent integer exponents describe z0, z1 and z2. Forward expands z0^-1 delta((z1-z2)/z0) in nonnegative z2 powers; reverse expands z0^-1 delta((z2-z1)/(-z0)) in nonnegative z1 powers; iterate expands z2^-1 delta((z1-z0)/z2) in nonnegative z0 powers. All integer mode indices and the complete exponent fibers are retained.

coefficient_extract is an unconditional equivalence reindexing identity with an unused finite-support binder; it does not prove finiteness. Actual coefficient-fiber finiteness is proved independently by coefficient_support, region_finite_modes, region_finite and region_fiber_finite, and is used by vector additivity and scalar linearity.

The deltaFiber_subsingleton instance is consumed implicitly by Set.toFinite in delta_fiber_finite and by Subsingleton.elim in delta_coefficient. Its absence from a lexical name scan is not an absence of proof-term consumption.

The bc carrier is the unchanged actual polarized Fock carrier, with arbitrary finite-support vectors and all integer indices. Homogeneous states have precisely the displayed parity membership premises. Mixed states use the existing two parity projections, not an assumed generic Jacobi identity, finite carrier, energy cutoff or surrogate state-field.

The signed product and mixed product are actual vector-valued coefficient distributions. Their operator-valued identities are the two required extensional End lifts, carrying zero duplicate Jacobi-proof credit. The previously accepted coefficient Borcherds proofs are reused, not re-proved or counted again.

mixed_resolved_finite is valid original immutable evidence with only an audit citation and no production consumer. It is not retained as a standalone canonical theorem target. The original source, all 61 declarations and all 37 theorem receipts remain evidence; the canonical credited increment has 60 authored declarations and 36 theorem targets.

Native information-escape registration is unfinished under issue #15040. Mathematical compilation and report binding do not establish declared_validated registration, frozen admission, CI, remote acceptance or repair of that issue. This is not a full VOA/CFT/string, emergent-spacetime or AdS/CFT completion; the original larger goal remains active and open.

**Definition 1.1 (Exponent).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.Exponent`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.Exponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three independent integer exponents; no support restriction imposed on distributions.

**Definition 1.2 (Distribution).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.Distribution`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.Distribution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All functions Exponent → Space, not a HahnSeries or a well-ordered three-variable series.

**Definition 1.3 (modeExponent).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.modeExponent`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.modeExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact triple (-n-1,-m-1,-k-1), with all three parameters in ℤ.

**Definition 1.4 (exponentAdd).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.exponentAdd`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.exponentAdd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Componentwise exponent addition records monomial multiplication only.

**Definition 1.5 (Region).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.Region`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.Region` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward, reverse and iterate expansion regions are separate constructors.

**Definition 1.6 (Atom).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.Atom`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.Atom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Independent delta power, nonnegative binomial offset and two field-mode integers.

**Definition 1.7 (deltaExponent).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaExponent`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Correct three-region monomial exponent formulas, defined before coefficient Jacobi.

**Theorem 1.8 (epsilon neg).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.epsilon_neg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.epsilon_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Elementary integer parity normalization (-1)^(-t)=(-1)^t; not an independent research endpoint. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.reverse_resolved. This consumed support has no separate mathematical-discovery credit.

**Definition 1.9 (deltaWeight).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaWeight`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Binomial weights; reverse has epsilon(-power), iterate keeps the raw binomial weight.

**Theorem 1.10 (deltaExponent injective).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaExponent_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaExponent_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Region-by-region integer equations determine the pure delta power and offset uniquely. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.FormalDeltaDistribution.deltaFiber_subsingleton. This consumed support has no separate mathematical-discovery credit.

**Definition 1.11 (deltaFiber).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaFiber`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual equality fiber for pure delta exponents; empty outside their image.

**Definition 1.12 (deltaFiber subsingleton).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaFiber_subsingleton`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaFiber_subsingleton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The instance is genuinely consumed implicitly: pure delta fibers are subsingletons, hence finite. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.FormalDeltaDistribution.delta_fiber_finite, D5.S3.VertexAlgebra.FormalDeltaDistribution.delta_coefficient. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.13 (delta fiber finite).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.delta_fiber_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.delta_fiber_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real finite scalar support on a subsingleton fiber, not global finiteness of the delta distribution. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.FormalDeltaDistribution.deltaDistribution, D5.S3.VertexAlgebra.FormalDeltaDistribution.delta_coefficient. This consumed support has no separate mathematical-discovery credit.

**Definition 1.14 (deltaDistribution).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaDistribution`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaDistribution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Scalar coefficient is an explicit finite sum over its actual exponent fiber.

**Theorem 1.15 (delta coefficient).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.delta_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.delta_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves that each pure delta monomial coefficient is precisely its prescribed region weight, including zero weights. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.forward_resolved, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.reverse_resolved, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.iterate_resolved.

**Definition 1.16 (fieldExponent).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.fieldExponent`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.fieldExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Product regions use x1,x2 modes; iterate uses x0,x2 modes.

**Definition 1.17 (atomExponent).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.atomExponent`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.atomExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual delta exponent plus actual field exponent, not a borrowed Borcherds index alias.

**Definition 1.18 (resolvedAtom).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolvedAtom`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolvedAtom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Solves the three linear exponent equations separately, for every exponent and offset.

**Theorem 1.19 (resolved exponent).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_exponent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Forward map lands in the actual coefficient fiber for all three regions. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.FormalDeltaDistribution.fiberEquiv. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.20 (exponent fiber unique).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.exponent_fiber_unique`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.exponent_fiber_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All atoms in a coefficient fiber are uniquely determined by their offset. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.FormalDeltaDistribution.fiberEquiv, D5.S3.VertexAlgebra.FormalDeltaDistribution.coefficient_support. This consumed support has no separate mathematical-discovery credit.

**Definition 1.21 (coefficientFiber).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficientFiber`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficientFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All delta/field convolution atoms whose combined exponent is the requested triple.

**Definition 1.22 (fiberEquiv).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.fiberEquiv`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.fiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

True ℕ-equivalence of the infinite convolution fiber; no assertion that the whole fiber is finite.

**Definition 1.23 (coefficientAction).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficientAction`

*Formalization.* `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficientAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Generic finsum over the convolution fiber; standalone infinite amplitudes retain Mathlib finsum conventions. Actual bc applications have separately proved finite support.

**Theorem 1.24 (coefficient support).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficient_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficient_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transports finite resolved-offset support to the real fiber using injectivity and the inverse equation. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.region_fiber_finite. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.25 (coefficient extract).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficient_extract`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficient_extract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual fiber reindexing by finsum_comp_equiv. Its finite hypothesis is unused in the proof; the identity is valid even without it, and this lemma alone is not a finiteness proof. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.forward_coefficient, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.reverse_coefficient, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.iterate_coefficient, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.signed_coefficient_resolved_sum.

**Theorem 1.26 (resolved forward).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_forward`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Solved modes t=n, p=m+n-i, q=k+i at the exact target exponent. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.forward_resolved. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.27 (resolved reverse).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_reverse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Solved modes t=n, p=m+i, q=k+n-i; reverse operator order is handled by atomOperator. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.reverse_resolved. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.28 (resolved iterate).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_iterate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Solved t=i-m-1, p=n+i, q=m+k-i, with no positivity restriction on n,m,k. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.iterate_resolved. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.29 (signed negative binomial).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.signed_negative_binomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.signed_negative_binomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uses generalized integer choose_neg to prove (-1)^i choose(i-m-1,i)=choose(m,i), cancelling two (-1)^i factors. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.iterate_resolved.

**Theorem 1.30 (modeExponent surjective).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.modeExponent_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.modeExponent_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every exponent occurs; coefficient checks do not cover merely a quadrant or restricted residue modes. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.FormalDeltaDistribution.distribution_eq_iff_modes, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.region_finite. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.31 (distribution eq iff modes).**

Lean statement: `D5/S3/VertexAlgebra/FormalDeltaDistribution.distribution_eq_iff_modes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalDeltaDistribution.distribution_eq_iff_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Generic extensional equality is exactly equality at all integer-mode triples. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.distribution_jacobi_iff_borcherds, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.mixed_distribution_jacobi_iff_borcherds. This consumed support has no separate mathematical-discovery credit.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.Atom`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.Distribution`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.Exponent`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.Region`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.atomExponent`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficientAction`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficientFiber`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficient_extract`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.coefficient_support`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaDistribution`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaExponent`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaExponent_injective`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaFiber`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaFiber_subsingleton`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.deltaWeight`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.delta_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.delta_fiber_finite`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.distribution_eq_iff_modes`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.epsilon_neg`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.exponentAdd`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.exponent_fiber_unique`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.fiberEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.fieldExponent`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.modeExponent`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.modeExponent_surjective`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolvedAtom`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_exponent`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_forward`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_iterate`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.resolved_reverse`
- Truth anchor: `D5/S3/VertexAlgebra/FormalDeltaDistribution.signed_negative_binomial`
