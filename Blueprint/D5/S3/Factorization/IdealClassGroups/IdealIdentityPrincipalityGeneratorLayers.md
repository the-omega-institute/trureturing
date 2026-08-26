# Ideal Identity, Principality, and Generator Coordinates

## Abstract

Prime valuations identify an ideal, the class group detects principality, and a unit coordinate relative to a nonzero generator identifies the exact generator.

**Theorem 1.1 (All prime-ideal valuations recover the fractional ideal).**

$$\forall I, J,\\{}(\forall p, \operatorname{valuation}\left(p, I\right) = \operatorname{valuation}\left(p, J\right)) \Rightarrow I = J.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.ideal_valuation_layer_recovers_fractional_ideal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is a direct reuse of the existing D5 faithfulness theorem; no factorization or injectivity argument is repeated here.

**Theorem 1.2 (The trivial class is exactly the principal locus).**

$$\operatorname{IsPrincipal}\left(I\right) \iff \operatorname{ClassGroupMk}\left(I\right) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.class_group_layer_detects_principality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported principal-ideal criterion separates knowing an ideal from knowing that it admits a global generator.

**Theorem 1.3 (Ideal identity does not imply principality).**

$$\exists I: \operatorname{Ideal}\left(QuadraticOrder\right), I = normTwoIdeal \land \operatorname{LocallyPrincipal}\left(I\right) \land \neg \operatorname{IsPrincipal}\left(I\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.identified_ideal_need_not_be_principal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named norm-two ideal in the quadratic order is already completely identified and principal at every nonzero-prime localization, yet the imported local-global theorem proves it is not principal.

**Theorem 1.4 (The first strictness disappears in a PID).**

$$\neg \exists I: \operatorname{Ideal}\left(\mathbb{Z}\right), \neg \operatorname{IsPrincipal}\left(I\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.nontrivial_class_group_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every ideal of the integers is principal, so the nonprincipal-ideal witness necessarily depends on leaving the trivial-class-group case.

**Theorem 1.5 (Principality does not choose a generator).**

$$\exists x, y\in \mathbb{Z}, x \neq y \land \operatorname{IdealSpan}\left(x\right) = \operatorname{IdealSpan}\left(y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.principality_does_not_determine_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integers one and minus one are distinct associates and generate the same ideal. The proof uses Mathlib's singleton-span theorem.

**Theorem 1.6 (Distinct unit coordinates require a nontrivial unit group).**

$$\neg \exists u: \operatorname{Units}\left(\operatorname{ZMod}\left(2\right)\right), u \neq 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.nontrivial_unit_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit group of ZMod two is a singleton. This concrete audit records the degenerate case in which the second strictness witness cannot exist.

**Theorem 1.7 (Changing the unit coordinate preserves the ideal).**

$$\forall a, u, \operatorname{IdealSpan}\left(\operatorname{UnitAction}\left(a, u\right)\right) = \operatorname{IdealSpan}\left(a\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.unit_coordinate_preserves_principal_ideal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by a unit uses Mathlib's exact singleton-span lemma and needs only a commutative semiring, not a field or a domain.

**Theorem 1.8 (The ideal and unit coordinate recover the exact generator).**

$$a \neq 0 \land \operatorname{IdealSpan}\left(b\right) = \operatorname{IdealSpan}\left(a\right) \Rightarrow\\{}\exists! u, \operatorname{UnitAction}\left(a, u\right) = b.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.ideal_and_unit_coordinate_recover_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal singleton spans first yield associated generators. A nonzero base in a domain then cancels, making the associated unit coordinate unique.

**Theorem 1.9 (A zero generator cannot have a unique unit coordinate).**

$$\neg \exists! u: \operatorname{Units}\left(\mathbb{Z}\right), \operatorname{UnitAction}\left(0, u\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.nonzero_generator_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over the integers, both unit coordinates one and minus one send the zero base to zero. Thus the nonzero-base hypothesis is necessary.

**Theorem 1.10 (A nonzero zero divisor can have a unit stabilizer).**

$$\exists a, b: \operatorname{ZMod}\left(8\right),\\{}a \neq 0 \land \operatorname{IdealSpan}\left(b\right) = \operatorname{IdealSpan}\left(a\right) \land \neg \exists! u: \operatorname{Units}\left(\operatorname{ZMod}\left(8\right)\right), \operatorname{UnitAction}\left(a, u\right) = b.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.no_zero_divisors_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In ZMod eight, the nonzero element four is fixed by both unit coordinates one and minus one. Nonzeroness alone therefore cannot replace the domain condition.

**Theorem 1.11 (A zero element excludes the empty carrier).**

$$\forall R, \operatorname{Zero}\left(R\right) \Rightarrow \operatorname{Nonempty}\left(R\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.zero_carrier_is_not_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty-type audit is definitional: the structure supplies its zero element. There is no natural-number parameter to audit at zero.

## References

- Truth anchor: `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.class_group_layer_detects_principality`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.ideal_and_unit_coordinate_recover_generator`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.ideal_valuation_layer_recovers_fractional_ideal`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.identified_ideal_need_not_be_principal`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.no_zero_divisors_is_necessary`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.nontrivial_class_group_is_necessary`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.nontrivial_unit_is_necessary`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.nonzero_generator_is_necessary`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.principality_does_not_determine_generator`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.unit_coordinate_preserves_principal_ideal`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.zero_carrier_is_not_empty`
- Dependency: [D5/S3/Factorization/Embeddings/FractionalIdealPrimeValuationFaithfulness](../Embeddings/FractionalIdealPrimeValuationFaithfulness.md)
- Dependency: [D5/S3/Factorization/IdealClassGroups/PrincipalIdealCriterion](PrincipalIdealCriterion.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/NormTwoIdealLocalGlobalGap](../QuadraticIdeals/NormTwoIdealLocalGlobalGap.md)
