# Unified Causal Catalog

## Abstract

Unified causal catalogs expose cumulative kernels and layered captures without census dependencies.

**Definition 1.1 (Observation analysis unit).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedObservationUnit`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedObservationUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A singleton CUT bundle carries exactly the cumulative observation kernel.

**Definition 1.2 (Intervention analysis unit).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedInterventionUnit`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedInterventionUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A singleton CUT bundle carries exactly the cumulative intervention kernel.

**Definition 1.3 (Counterfactual analysis unit).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedCounterfactualUnit`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedCounterfactualUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A singleton CUT bundle carries exactly the cumulative counterfactual kernel.

**Definition 1.4 (Cumulative analysis catalog).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedCumulativeCatalog`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedCumulativeCatalog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The flat analysis view contains observation, intervention, and counterfactual readouts.

**Definition 1.5 (Unified OI theorem unit).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedObservationInterventionUnit`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedObservationInterventionUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The frozen observation-intervention theorem is transported to the shared arena.

**Definition 1.6 (Unified IC theorem unit).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedInterventionCounterfactualUnit`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedInterventionCounterfactualUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The frozen intervention-counterfactual theorem is transported to the shared arena.

**Definition 1.7 (Frozen transition catalog).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedFrozenTransitionCatalog`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedFrozenTransitionCatalog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical theorem catalog contains exactly the two faithful frozen occurrences.

**Theorem 1.8 (The frozen transition catalog is irredundant).**

$$CatalogIrredundant\left(unifiedFrozenTransitionCatalog\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unified_frozen_transition_catalog_irredundant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two named branch-local witnesses each separate one occurrence while remaining invisible to the other.

**Definition 1.9 (Unified off-diagonal pairs).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedOffDiagonalPairs`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedOffDiagonalPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All ordered pairs of distinct states form the 2,256-pair denominator.

**Definition 1.10 (Observation escape set).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.E_obs`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.E_obs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These off-diagonal pairs have equal cumulative observation readouts.

**Definition 1.11 (Intervention escape set).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.E_int`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.E_int` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These off-diagonal pairs have equal cumulative intervention readouts.

**Definition 1.12 (Counterfactual escape set).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.E_cf`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.E_cf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These off-diagonal pairs have equal cumulative counterfactual readouts.

**Definition 1.13 (Observation layer).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.L_obs`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.L_obs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first layer captures pairs already separated by observation.

**Definition 1.14 (Intervention layer).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.L_int`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.L_int` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The middle layer captures observation collisions separated by intervention.

**Definition 1.15 (Counterfactual layer).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.L_cf`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.L_cf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The final layer captures intervention collisions separated by counterfactual data.

**Definition 1.16 (Counterfactual capture set).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.capturedByCounterfactual`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.capturedByCounterfactual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the complement of the finest escape kernel inside the denominator.

**Theorem 1.17 (Layered increments are pairwise disjoint).**

$$Disjoint\left(L_{obs}, L_{int}\right) \land Disjoint\left(L_{obs}, L_{cf}\right) \land Disjoint\left(L_{int}, L_{cf}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unified_layered_increments_pairwise_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nested factorization prevents any ordered pair from first appearing in two layers.

**Theorem 1.18 (Layered increments partition counterfactual capture).**

$$union\left(union\left(L_{obs}, L_{int}\right), L_{cf}\right) = capturedByCounterfactual.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unified_layered_increments_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every pair outside the counterfactual kernel appears in exactly one cumulative layer.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.E_cf`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.E_int`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.E_obs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.L_cf`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.L_int`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.L_obs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.capturedByCounterfactual`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedCounterfactualUnit`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedCumulativeCatalog`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedFrozenTransitionCatalog`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedInterventionCounterfactualUnit`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedInterventionUnit`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedObservationInterventionUnit`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedObservationUnit`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unifiedOffDiagonalPairs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unified_frozen_transition_catalog_irredundant`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unified_layered_increments_pairwise_disjoint`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.unified_layered_increments_partition`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/Laws](../InformationEscape/Laws.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment](UnifiedCausalAlignment.md)
