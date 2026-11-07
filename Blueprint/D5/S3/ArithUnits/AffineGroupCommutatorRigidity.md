# Affine Group Commutators and Support Rigidity in Prime Residue Fields

## Abstract

Affine group commutators and support rigidity in prime residue fields.

**Theorem 1.1 (The affine commutator is a translation).**

$$\forall p \in Nat, a \in ZMod\left(p\right), b \in ZMod\left(p\right), c \in ZMod\left(p\right), d \in ZMod\left(p\right), x \in ZMod\left(p\right),\; centeredAffine\left(a, c, centeredAffine\left(b, d, x\right)\right) = centeredAffine\left(b, d, centeredAffine\left(a, c, x\right)\right) + commutatorShift\left(a, b, c, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.centeredAffine_commutator_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two centered affine compositions have equal multiplier and differ by the translation (a-1)(b-1)(c-d).

**Theorem 1.2 (Centered affine maps commute only in the degenerate cases).**

$$\forall p \in Nat, a \in ZMod\left(p\right), b \in ZMod\left(p\right), c \in ZMod\left(p\right), d \in ZMod\left(p\right),\; commutatorShift\left(a, b, c, d\right) = 0 \Leftrightarrow \left(a = 1 \lor \left(b = 1 \lor c = d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.commutatorShift_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a prime residue field, vanishing of the commutator is equivalent to a trivial multiplier, b trivial, or equal centers.

**Theorem 1.3 (Invariant supports inherit the commutator translation).**

$$\forall p \in Nat, D \in Finset\left(ZMod\left(p\right)\right), a \in ZMod\left(p\right), b \in ZMod\left(p\right), c \in ZMod\left(p\right), d \in ZMod\left(p\right),\; \left(image\left(D, centeredAffine\left(a, c\right)\right) = D \land image\left(D, centeredAffine\left(b, d\right)\right) = D\right) \Rightarrow image\left(D, translateBy\left(commutatorShift\left(a, b, c, d\right)\right)\right) = D$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.affine_commutator_translation_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the two invariant images transports the ring identity to a Finset translation action.

**Theorem 1.4 (Nontrivial distinct centers force p-divisibility).**

$$\forall p \in Nat, D \in Finset\left(ZMod\left(p\right)\right), a \in ZMod\left(p\right), b \in ZMod\left(p\right), c \in ZMod\left(p\right), d \in ZMod\left(p\right),\; \left(image\left(D, centeredAffine\left(a, c\right)\right) = D \land \left(image\left(D, centeredAffine\left(b, d\right)\right) = D \land \left(\left(a \ne 1 \land b \ne 1\right) \land c \ne d\right)\right)\right) \Rightarrow p \mid card\left(D\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.card_dvd_of_nontrivial_distinct_center_affine_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero translation in characteristic p annihilates the degree-zero moment, so p divides the support cardinality.

**Theorem 1.5 (Prime-field invariant supports are empty or full).**

$$\forall p \in Nat, D \in Finset\left(ZMod\left(p\right)\right), a \in ZMod\left(p\right), b \in ZMod\left(p\right), c \in ZMod\left(p\right), d \in ZMod\left(p\right),\; \left(image\left(D, centeredAffine\left(a, c\right)\right) = D \land \left(image\left(D, centeredAffine\left(b, d\right)\right) = D \land \left(\left(a \ne 1 \land b \ne 1\right) \land c \ne d\right)\right)\right) \Rightarrow \left(D = emptyFinset\left(\right) \lor D = univFinset\left(ZMod\left(p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.distinct_center_affine_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The p-divisibility conclusion and the p-element field-size bound leave only the empty and universal supports.

**Theorem 1.6 (Cardinalities outside the p-divisible class are impossible).**

$$\forall p \in Nat, n \in Nat, D \in Finset\left(ZMod\left(p\right)\right), a \in ZMod\left(p\right), b \in ZMod\left(p\right), c \in ZMod\left(p\right), d \in ZMod\left(p\right),\; \left(card\left(D\right) = n \land \left(image\left(D, centeredAffine\left(a, c\right)\right) = D \land \left(image\left(D, centeredAffine\left(b, d\right)\right) = D \land \left(\left(a \ne 1 \land b \ne 1\right) \land \left(c \ne d \land \left(\neg p \mid n\right)\right)\right)\right)\right)\right) \Rightarrow False$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.no_card_not_dvd_of_nontrivial_distinct_center_affine_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The divisibility theorem immediately excludes any prescribed cardinality that is not divisible by p.

This package isolates the affine group commutator and its arithmetic support consequence for every prime residue field. It does not claim that the two multipliers generate the full multiplicative group or formalize a projective-plane existence theorem.

## References

- Truth anchor: `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.affine_commutator_translation_invariant`
- Truth anchor: `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.card_dvd_of_nontrivial_distinct_center_affine_invariant`
- Truth anchor: `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.centeredAffine_commutator_formula`
- Truth anchor: `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.commutatorShift_eq_zero_iff`
- Truth anchor: `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.distinct_center_affine_classification`
- Truth anchor: `D5/S3/ArithUnits/AffineGroupCommutatorRigidity.no_card_not_dvd_of_nontrivial_distinct_center_affine_invariant`
- Dependency: [D5/S3/ArithUnits/TranslationInvariantLowMoments](TranslationInvariantLowMoments.md)
