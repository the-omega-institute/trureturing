# Type-A Fixed SLn Power

## Abstract

Type-A Fixed SLn Power.

PartII Section5, printed pp249--251: actual type-A fixed qth powers. The paper cites [SW] for Lemma5.1. Here the stated type-A power-form class estimate is proved independently by explicit reflected permutation matrices, exact centralizer row coordinates, the Uplus chart and an injective UL big cell. No SW/LS2/class-width/CFSG input is assumed. The original finite-outer value construction is consumed with original q/e powers and one correction before all witnesses. Full class-width and all-simple uniform scalar product remain unproved.

**Definition 1.1 (fixedElement).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.fixedElement`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.fixedElement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A characteristic-independent, actual determinant-one permutation matrix in the D0PhiGamma fixed subgroup. Its two reflected cycles have length q+1, fix both boundary coordinates, and preserve height parity.

**Theorem 1.2 (actual fixed element).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_element`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_element` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual full boundary-diagonal, field and positive-graph actions fix the constructed matrix. No fixed-element law is assumed.

**Theorem 1.3 (actual fixed power nonidentity).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_power_nonidentity`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_power_nonidentity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Its qth power is nonidentity for EVERY positive q, independently of characteristic. This does not assert the still-missing large-class bound.

**Theorem 1.4 (actual fixed power noncentral).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_power_noncentral`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_power_noncentral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The qth power is genuinely noncentral, not merely nonidentity.

**Theorem 1.5 (actual small field fixed power values).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_small_field_fixed_power_values`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_small_field_fixed_power_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual original selected Fin/q-over-e value construction in the small-field branch, now with a constructed fixed element and noncentral qth power. The rank-independent finite-outer bound and one correction are genuine. This is value range, not the unproved uniform class width.

**Theorem 1.6 (actual fixed centralizer card).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_centralizer_card`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_centralizer_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual centralizer coordinates: every row of a commuting matrix is reconstructed from the two long-cycle base rows and untouched rows. This derives an injection; no centralizer-size estimate is assumed.

**Theorem 1.7 (actual q power centralizer card).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_centralizer_card`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_centralizer_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coprimality is implemented by (z^q)^r=z^-1 for a cycle of length qr+1. Thus the ACTUAL qth-power centralizer has the same row bound.

**Theorem 1.8 (actual q power class lower).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_class_lower`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_class_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quantitative actual conjugacy class of the fixed qth power. The centralizer rows and genuine UL big-cell lower bound give this estimate; no SW/LS2 power-class or class-width theorem is assumed.

**Theorem 1.9 (actual q power large class).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_large_class`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_large_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An elementary type-A Lemma5.1 bound in power form: when qr>=k+2, |SLn(F)|<=|class(z^q)|^8, with z fixed by the constructed D0PhiGamma. The class-width theorem is a separate, still-unproved obligation.

**Theorem 1.10 (actual small field large class values).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_small_field_large_class_values`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_small_field_large_class_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Section5's actual long-cycle value consumer, with the quantitative class estimate conjoined and the fixed-element law proved. R remains the number of desired ordinary valueS; uniform class width is not assumed.

**Theorem 1.11 (actual all large rank fixed power).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_all_large_rank_fixed_power`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_all_large_rank_fixed_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All sufficiently large actual ranks, with no rank congruence premise. The Euclidean decomposition constructs the two long cycles; z and its large qth-power class are chosen before EVERY boundary DFG action.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_all_large_rank_fixed_power`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_centralizer_card`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_element`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_power_noncentral`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_fixed_power_nonidentity`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_centralizer_card`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_class_lower`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_q_power_large_class`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_small_field_fixed_power_values`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.actual_small_field_large_class_values`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower.fixedElement`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction](../Unitriangular/PartIIOuterSLnAction.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnBigCellCard](../Unitriangular/PartIISLnBigCellCard.md)
