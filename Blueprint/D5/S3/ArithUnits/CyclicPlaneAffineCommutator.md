# Affine Commutators and Translation Rigidity Modulo 157

## Abstract

Affine commutators and translation rigidity modulo 157.

**Theorem 1.1 (The affine commutator is a translation).**

$$\forall D \in Finset\left(ZMod\left(157\right)\right), c \in ZMod\left(157\right), d \in ZMod\left(157\right),\; \left(image\left(D, affineDouble\left(c\right)\right) = D \land image\left(D, affineTriple\left(d\right)\right) = D\right) \Rightarrow image\left(D, translateBy\left(2 \cdot \left(c - d\right)\right)\right) = D$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/CyclicPlaneAffineCommutator.affine_commutator_translation_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two compositions have the same multiplier six. Comparing their constant terms turns equality of their invariant images into invariance under translation by 2(c-d).

**Theorem 1.2 (Distinct centers force cardinality divisibility by 157).**

$$\forall D \in Finset\left(ZMod\left(157\right)\right), c \in ZMod\left(157\right), d \in ZMod\left(157\right),\; \left(image\left(D, affineDouble\left(c\right)\right) = D \land \left(image\left(D, affineTriple\left(d\right)\right) = D \land c \ne d\right)\right) \Rightarrow 157 \mid card\left(D\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/CyclicPlaneAffineCommutator.card_dvd_of_distinct_center_affine_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct centers the commutator translation is nonzero. The degree-zero translation moment vanishes in characteristic 157, so the finite-set cardinality is zero modulo 157.

**Theorem 1.3 (Distinct-center invariant supports are empty or full).**

$$\forall D \in Finset\left(ZMod\left(157\right)\right), c \in ZMod\left(157\right), d \in ZMod\left(157\right),\; \left(image\left(D, affineDouble\left(c\right)\right) = D \land \left(image\left(D, affineTriple\left(d\right)\right) = D \land c \ne d\right)\right) \Rightarrow \left(D = emptyFinset\left(\right) \lor D = univFinset\left(ZMod\left(157\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/CyclicPlaneAffineCommutator.distinct_center_affine_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A subset of the 157-element field has cardinality at most 157. Combining this bound with 157-divisibility leaves only the empty and full sets.

**Theorem 1.4 (Thirteen elements cannot support distinct affine centers).**

$$\forall D \in Finset\left(ZMod\left(157\right)\right), c \in ZMod\left(157\right), d \in ZMod\left(157\right),\; \left(card\left(D\right) = 13 \land \left(image\left(D, affineDouble\left(c\right)\right) = D \land \left(image\left(D, affineTriple\left(d\right)\right) = D \land c \ne d\right)\right)\right) \Rightarrow False$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/CyclicPlaneAffineCommutator.no_thirteen_element_distinct_center_affine_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The divisibility theorem immediately rules out cardinality thirteen. This is the affine noncommutation consequence used by the projective-plane application.

The module isolates the affine group commutator and its additive orbit consequence. It does not formalize the First Multiplier Theorem, the Singer correspondence, or arbitrary projective-plane nonexistence.

## References

- Truth anchor: `D5/S3/ArithUnits/CyclicPlaneAffineCommutator.affine_commutator_translation_invariant`
- Truth anchor: `D5/S3/ArithUnits/CyclicPlaneAffineCommutator.card_dvd_of_distinct_center_affine_invariant`
- Truth anchor: `D5/S3/ArithUnits/CyclicPlaneAffineCommutator.distinct_center_affine_classification`
- Truth anchor: `D5/S3/ArithUnits/CyclicPlaneAffineCommutator.no_thirteen_element_distinct_center_affine_invariant`
- Dependency: [D5/S3/ArithUnits/TranslationInvariantLowMoments](TranslationInvariantLowMoments.md)
