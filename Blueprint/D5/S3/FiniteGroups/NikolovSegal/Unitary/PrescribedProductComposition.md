# Prescribed Product Composition

## Abstract

In an arbitrary group, ordered corrected automorphism value sets concatenate through Fin-indexed tuples. The proof transports corrections through genuine inner automorphisms and retains target-independent correction choices. These helpers are consumed by the five-block intrinsic SU construction.

**Definition 1.1 (Covers).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.Covers`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.Covers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One genuine right-inner correction is selected before all targets in T. The full prescribed tuple and original divisor powers are retained.

**Theorem 1.2 (covers append).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.covers_append`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.covers_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consume two consecutive coverage blocks without reordering their values. The resulting correction still precedes every target of the set product.

**Theorem 1.3 (covers of left inner).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.covers_of_left_inner`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.covers_of_left_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A genuine left inner change of the supplied automorphisms can be absorbed into right-inner corrections, before any target is chosen.

The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.Covers`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.covers_append`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.covers_of_left_inner`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge](../CosetPowerBridge.md)
