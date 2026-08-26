# Finite Marginal Global Readout Contrast

## Abstract

Finite compatible marginals need not be globally realizable by a readout image.

**Theorem 1.1 (The finite-subset readout image is measurable).**

$$\operatorname{MeasurableSet}\left(\operatorname{range}\left(readout\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.readout_image_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite-subset domain is countable, so its readout range is a countable measurable set in the countable-coordinate product.

**Theorem 1.2 (Every finite marginal is a probability measure).**

$$\forall J: FinsetNat, \operatorname{IsProbabilityMeasure}\left(finiteMarginal(J)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.finite_marginal_family_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each finite coordinate law is the finite product of the fair Bernoulli probability measure.

**Theorem 1.3 (Finite marginals are the restrictions of the product law).**

$$\forall J: FinsetNat, \operatorname{map}\left(\operatorname{restrict}\left(J\right), fairProduct\right) = finiteMarginal(J)..$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.finite_marginal_family_compatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's infinite product restriction theorem supplies the compatibility equation directly.

**Theorem 1.4 (The finite-subset image has zero product measure).**

$$fairProduct(\operatorname{range}\left(readout\right)) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.readout_image_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every readout has finite support, whereas independent activation events occur infinitely often almost surely.

**Theorem 1.5 (The identity readout is the positive comparison).**

$$fairProduct(\operatorname{range}\left(identityReadout\right)) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.identity_readout_image_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity readout is surjective onto the full path space, so its image is the whole probability space.

**Theorem 1.6 (The constant readout has null image in the fair product).**

$$fairProduct(\operatorname{range}\left(constantReadout\right)) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.constant_readout_image_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant readout has singleton, hence finitely supported, image; the product assigns that image zero mass.

**Theorem 1.7 (Surjectivity forces full image measure).**

$$Surjective(q) \Rightarrow nu(\operatorname{range}\left(q\right)) = nu(univ).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.surjective_readout_has_full_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the general image audit: no measurability or probability assumption is needed for the set equality itself.

**Theorem 1.8 (The finite-index readout is surjective).**

$$Surjective(finiteReadout(J)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.finite_readout_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite J, filtering the finite universe by a Boolean path constructs a preimage for every path.

**Theorem 1.9 (Finite index gives full image for the canonical finite readout).**

$$finiteMarginal(J)(\operatorname{range}\left(finiteReadout(J)\right)) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.finite_index_readout_image_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This includes J equal to the empty finset, so zero index is explicitly covered.

**Theorem 1.10 (An empty domain has empty readout image).**

$$\operatorname{range}\left(q\right) = emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.empty_domain_readout_image_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty-domain case cannot be conull for a probability measure.

**Theorem 1.11 (A one-point domain has singleton image).**

$$\operatorname{range}\left(q\right) = \operatorname{singleton}\left(q(unit)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.singleton_domain_readout_image_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every map from PUnit is constant, making the singleton image explicit rather than silently assuming surjectivity.

**Theorem 1.12 (Finite compatibility does not imply global realizability).**

$$\forall J: FinsetNat, \operatorname{IsProbabilityMeasure}\left(finiteMarginal(J)\right). \land \forall J: FinsetNat, \operatorname{map}\left(\operatorname{restrict}\left(J\right), fairProduct\right) = finiteMarginal(J).. \land \operatorname{MeasurableSet}\left(\operatorname{range}\left(readout\right)\right) \land fairProduct(\operatorname{range}\left(readout\right)) = 0 \land fairProduct(\operatorname{range}\left(identityReadout\right)) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.fpod_principle_120_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem combines probability of every finite marginal, exact restriction compatibility, measurability of the image, the null counterexample, and the conull identity comparison.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.constant_readout_image_null`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.empty_domain_readout_image_empty`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.finite_index_readout_image_full`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.finite_marginal_family_compatible`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.finite_marginal_family_probability`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.finite_readout_surjective`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.fpod_principle_120_1`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.identity_readout_image_full`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.readout_image_measurable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.readout_image_null`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.singleton_domain_readout_image_singleton`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.surjective_readout_has_full_image`
