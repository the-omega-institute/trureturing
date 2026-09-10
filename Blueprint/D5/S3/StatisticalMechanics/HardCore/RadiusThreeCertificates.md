# RadiusThreeCertificates

## Abstract

Geometric hard-core branching, exact certificates and their precise scope.

**Definition 1.1 (Actual blocked vertices).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeMask`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit integer code decodes to a finite subset of the Manhattan radius-three disk.

**Definition 1.2 (Geometrically computed transitions).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeStep`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An unblocked move computes memoryStep and looks up its exact encoded successor. The closure theorem proves that this lookup cannot omit a legal move.

**Definition 1.3 (All-order sub-potential).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeLower`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeLower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nonnegative integer weights certify a lower rate for every allowed ordering. Zero weights are allowed on dead states.

**Definition 1.4 (Selected-policy super-potential).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeUpper`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeUpper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Strictly positive integer weights certify the chosen adaptive controller. Every state is checked.

**Definition 1.5 (Fixed-SRL sub-potential).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeFixedLower`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeFixedLower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A separate integer witness provides a lower growth rate for the same geometric memory model under fixed SRL ordering.

**Definition 1.6 (Concrete adaptive ordering).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeChoice`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeChoice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each represented blocked set selects one of the six permutations. This is an explicit stationary controller.

**Theorem 1.7 (Complete geometric closure).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement checks cardinality, distinct codes, the initial parent mask, parent and origin conditions, and every state-order-direction successor. This is closure of the finite geometric presentation, not sampled path coverage.

**Theorem 1.8 (Exact arithmetic certificates).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_potentials`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_potentials` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All-order lower rows use 5041 and 2000; selected-policy upper rows use 12603 and 5000; fixed-SRL lower rows use 25209 and 10000. Initial weights and the cap are one billion. The proof script requests kernel reduction of the actual data.

**Theorem 1.9 (An all-depth adaptive upper bound).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_adaptive_upper`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_adaptive_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the generic induction to the concrete selected controller. The conclusion retains the explicit state-dependent prefactor.

**Theorem 1.10 (A floor for every controller).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_all_controllers_lower`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_all_controllers_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From the initial state, every policy has at least the displayed exponential descendant count. The quantifier includes arbitrary dependence on the entire direction history. This lower bound belongs to the truncated memory model and cannot be transferred as a grid lower bound.

**Theorem 1.11 (A larger fixed-order lower bound).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_fixed_order_lower`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_fixed_order_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-SRL relaxed tree has lower rate 2.5209, exceeding the selected adaptive upper rate 2.5206. The all-depth integer inequalities imply the asymptotic comparison.

**Theorem 1.12 (An actual finite-grid-domain consumer).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_finite_domain_upper`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_finite_domain_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite integer-grid vertex domain with its parent absent, the actual ordered deletion count satisfies the explicit upper bound. Geometry discharges the table-coverage premises. Identification with the partition-function recursion and the complex zero-free transfer remain outside this theorem.

The sources were logically reviewed and the concrete certificates independently replayed using exact integers. Lean elaboration, axiom-print execution and Scribe emission were not performed in the authoring runtime. These candidate sources do not assert an improved global zero-free threshold.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeChoice`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeFixedLower`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeLower`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeMask`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeStep`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeUpper`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_adaptive_upper`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_all_controllers_lower`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_finite_domain_upper`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_fixed_order_lower`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_geometry`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_potentials`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory](OrderedGridMemory.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/RadiusThreeData](RadiusThreeData.md)
