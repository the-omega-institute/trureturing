# BcGhostFormalDeltaJacobi

## Abstract

Three-variable formal delta: BcGhostFormalDeltaJacobi

These declarations retain the accepted three-variable formal-delta construction. Canonical transport supplies no new mathematical credit. Declaration handles bind to compiled source; WithoutFormula does not display a formula or replace the full Lean statement and proof.

The three independent integer exponents describe z0, z1 and z2. Forward expands z0^-1 delta((z1-z2)/z0) in nonnegative z2 powers; reverse expands z0^-1 delta((z2-z1)/(-z0)) in nonnegative z1 powers; iterate expands z2^-1 delta((z1-z0)/z2) in nonnegative z0 powers. All integer mode indices and the complete exponent fibers are retained.

coefficient_extract is an unconditional equivalence reindexing identity with an unused finite-support binder; it does not prove finiteness. Actual coefficient-fiber finiteness is proved independently by coefficient_support, region_finite_modes, region_finite and region_fiber_finite, and is used by vector additivity and scalar linearity.

The deltaFiber_subsingleton instance is consumed implicitly by Set.toFinite in delta_fiber_finite and by Subsingleton.elim in delta_coefficient. Its absence from a lexical name scan is not an absence of proof-term consumption.

The bc carrier is the unchanged actual polarized Fock carrier, with arbitrary finite-support vectors and all integer indices. Homogeneous states have precisely the displayed parity membership premises. Mixed states use the existing two parity projections, not an assumed generic Jacobi identity, finite carrier, energy cutoff or surrogate state-field.

The signed product and mixed product are actual vector-valued coefficient distributions. Their operator-valued identities are the two required extensional End lifts, carrying zero duplicate Jacobi-proof credit. The previously accepted coefficient Borcherds proofs are reused, not re-proved or counted again.

mixed_resolved_finite is valid original immutable evidence with only an audit citation and no production consumer. It is not retained as a standalone canonical theorem target. The original source, all 61 declarations and all 37 theorem receipts remain evidence; the canonical credited increment has 60 authored declarations and 36 theorem targets.

Native information-escape registration is unfinished under issue #15040. Mathematical compilation and report binding do not establish declared_validated registration, frozen admission, CI, remote acceptance or repair of that issue. This is not a full VOA/CFT/string, emergent-spacetime or AdS/CFT completion; the original larger goal remains active and open.

**Definition 1.1 (atomOperator).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.atomOperator`

*Formalization.* `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.atomOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual scalar delta coefficient times the actual original Y product, reversed product, or iterated Y mode.

**Definition 1.2 (regionDistribution).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.regionDistribution`

*Formalization.* `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.regionDistribution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vector-valued action of the actual convolution atoms; no arbitrary distribution multiplication.

**Theorem 1.3 (forward resolved).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.forward_resolved`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.forward_resolved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Connects the independently solved forward atom and scalar delta coefficient to the actual Y first summand. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.region_finite_modes, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.forward_coefficient. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.4 (reverse resolved).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.reverse_resolved`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.reverse_resolved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Connects reversed Y order and epsilon(-n)=epsilon(n) to the second summand with exchange set to 1. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.region_finite_modes, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.reverse_coefficient. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.5 (iterate resolved).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.iterate_resolved`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.iterate_resolved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Connects the actual iterated Y mode to the accepted iterate summand after raw binomial normalization. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.region_finite_modes, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.iterate_coefficient. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.6 (region finite modes).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.region_finite_modes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.region_finite_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual truncation suppliers firstTerm_finite, secondTerm_finite and borcherds_left_finite give finite vector support. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.region_finite. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.7 (region finite).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.region_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.region_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extends real finite vector support to every exponent via modeExponent surjectivity. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.region_fiber_finite, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.signed_resolved_finite, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.signed_coefficient_resolved_sum. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.8 (region fiber finite).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.region_fiber_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.region_fiber_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite vector support on the genuine fiber, used in both additivity and scalar linearity. Bounds may depend on vector. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.regionDistribution_add, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.regionDistribution_smul. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.9 (forward coefficient).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.forward_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.forward_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derives Σ_i (-1)^i choose(n,i) a_(m+n-i)b_(k+i)v from the actual exponent fiber. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.signed_product_coefficient.

**Theorem 1.10 (reverse coefficient).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.reverse_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.reverse_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derives Σ_i epsilon(n)(-1)^i choose(n,i)b_(k+n-i)a_(m+i)v before the Koszul exchange factor. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.signed_product_coefficient.

**Theorem 1.11 (iterate coefficient).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.iterate_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.iterate_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derives Σ_i choose(m,i)(a_(n+i)b)_(m+k-i)v from the raw iterate expansion. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.distribution_jacobi_iff_borcherds, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.mixed_distribution_jacobi_iff_borcherds.

**Theorem 1.12 (regionDistribution add).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.regionDistribution_add`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.regionDistribution_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Genuine vector additivity uses finite-support addition on actual fibers; it is not an unsupported operator-valued finsum. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.operatorDistribution.

**Theorem 1.13 (regionDistribution smul).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.regionDistribution_smul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.regionDistribution_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Genuine complex scalar linearity uses smul_finsum with actual finite fiber support. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.operatorDistribution.

**Definition 1.14 (operatorDistribution).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.operatorDistribution`

*Formalization.* `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.operatorDistribution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Packages pointwise finite vector actions as End-valued coefficients; no uniform or global finite End sum.

**Definition 1.15 (signedProductDistribution).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signedProductDistribution`

*Formalization.* `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signedProductDistribution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Forward minus the original koszul(leftParity,rightParity) times reverse, with no new parity convention.

**Theorem 1.16 (signed product coefficient).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signed_product_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signed_product_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed coefficient assembly wrapper: separates finite sums and applies the actual Koszul factor. No independent discovery or duplicate endpoint credit. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.distribution_jacobi_iff_borcherds, D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.mixed_product_coefficient. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.17 (distribution jacobi iff borcherds).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.distribution_jacobi_iff_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.distribution_jacobi_iff_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact coefficient equivalence for independently defined actual distributions, using all integer modes and the three proved coefficient formulas. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.homogeneous_formal_delta_jacobi.

**Theorem 1.18 (homogeneous formal delta jacobi).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.homogeneous_formal_delta_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.homogeneous_formal_delta_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual homogeneous bc distribution identity; accepted Borcherds is applied only after independently constructed distribution/coefficient bridges. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.homogeneous_operator_formal_delta_jacobi.

**Definition 1.19 (mixedProductDistribution).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixedProductDistribution`

*Formalization.* `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixedProductDistribution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exactly four parityPart components, each with its own Koszul sign; vector has arbitrary parity.

**Definition 1.20 (signedResolvedTerm).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signedResolvedTerm`

*Formalization.* `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signedResolvedTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Resolved-offset signed difference, not a declaration of unrestricted distribution multiplication.

**Theorem 1.21 (signed resolved finite).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signed_resolved_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signed_resolved_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite union of actual forward/reverse supports, consumed by the mixed finsum/finite parity interchange. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.mixed_coefficient_resolved_sum. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.22 (signed coefficient resolved sum).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signed_coefficient_resolved_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signed_coefficient_resolved_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Correct supported subtraction/scalar interchange and actual fiber reindexing, consumed by the four-component resolved expansion. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.mixed_coefficient_resolved_sum.

**Definition 1.23 (mixedResolvedTerm).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixedResolvedTerm`

*Formalization.* `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixedResolvedTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite four-component sum of actual signed resolved terms.

**Theorem 1.24 (mixed coefficient resolved sum).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_coefficient_resolved_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_coefficient_resolved_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unconsumed but substantive requested coefficient endpoint: explicitly interchanges finsum with the finite four-component sum using signed_resolved_finite, not mixed_resolved_finite. It is not a thin support wrapper.

**Theorem 1.25 (mixed product coefficient).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_product_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_product_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Thin finite-parity simp/assembly wrapper, genuinely consumed by exact mixed equivalence; no separate independent result credit. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.mixed_distribution_jacobi_iff_borcherds. This consumed support has no separate mathematical-discovery credit.

**Theorem 1.26 (mixed distribution jacobi iff borcherds).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_distribution_jacobi_iff_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_distribution_jacobi_iff_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full mixed distribution/coefficient equivalence; the iterate uses unsplit original states while the product has four signed components. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.mixed_formal_delta_jacobi.

**Theorem 1.27 (mixed formal delta jacobi).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_formal_delta_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_formal_delta_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual arbitrary-state bc four-component identity follows from accepted mixed_borcherds and the new exact expansion bridge. Actual canonical proof or implicit consumers: D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi.mixed_operator_formal_delta_jacobi.

**Theorem 1.28 (homogeneous operator formal delta jacobi).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.homogeneous_operator_formal_delta_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.homogeneous_operator_formal_delta_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Thin LinearMap.ext/congrFun lift of the genuine vector identity, but retained as the expressly required End-valued endpoint. No extra independent proof or novelty credit. This required End lift carries zero duplicate Jacobi-proof credit.

**Theorem 1.29 (mixed operator formal delta jacobi).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_operator_formal_delta_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_operator_formal_delta_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Thin extensional lift with finite parity sum evaluation; retained as the expressly required mixed End endpoint, not credited as a second independent Jacobi proof. This required End lift carries zero duplicate Jacobi-proof credit.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.atomOperator`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.distribution_jacobi_iff_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.forward_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.forward_resolved`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.homogeneous_formal_delta_jacobi`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.homogeneous_operator_formal_delta_jacobi`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.iterate_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.iterate_resolved`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixedProductDistribution`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixedResolvedTerm`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_coefficient_resolved_sum`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_distribution_jacobi_iff_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_formal_delta_jacobi`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_operator_formal_delta_jacobi`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.mixed_product_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.operatorDistribution`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.regionDistribution`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.regionDistribution_add`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.regionDistribution_smul`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.region_fiber_finite`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.region_finite`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.region_finite_modes`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.reverse_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.reverse_resolved`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signedProductDistribution`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signedResolvedTerm`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signed_coefficient_resolved_sum`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signed_product_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFormalDeltaJacobi.signed_resolved_finite`
- Dependency: [D5/S3/VertexAlgebra/FormalDeltaDistribution](FormalDeltaDistribution.md)
