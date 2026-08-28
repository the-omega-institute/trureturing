# Three-Level Quantifier Separation

## Abstract

Finite Boolean systems strictly separate local witnesses, compatible families, and global sources.

**Theorem 1.1 (A compatible global readout supplies a compatible family).**

$$\operatorname{ReadoutsCompatible}\left(t, ell\right) \land \operatorname{GlobalSource}\left(ell, family\right) \Rightarrow \operatorname{CompatibleFamilyExists}\left(t\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation.global_source_implies_compatible_family_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A global source realizes the specified local family. The explicit ReadoutsCompatible premise transports that realization through every all-pairs transition equation.

**Theorem 1.2 (A compatible family supplies every local witness).**

$$\operatorname{CompatibleFamilyExists}\left(t\right) \Rightarrow \operatorname{LocalWitnesses}\left(Y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation.compatible_family_exists_implies_local_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choosing the simultaneous family already gives one inhabitant in each local type. This implication does not need the compatibility equations after the family has been obtained.

**Theorem 1.3 (Local witnesses need not form a compatible family).**

$$\operatorname{LocalWitnesses}\left(\operatorname{Fin}\left(2\right) \mapsto Bool\right) \land \neg \operatorname{CompatibleFamilyExists}\left(twistedTransition\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation.local_witnesses_do_not_imply_compatible_family_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Fin 2 with Boolean fibers, every coordinate is inhabited. Identity in one off-diagonal direction and negation in the reverse direction force contradictory equations for any chosen family.

**Theorem 1.4 (A compatible family need not have a global source).**

$$\operatorname{ReadoutsCompatible}\left(identityTransition, constantFalseReadout\right) \land \operatorname{CompatibleFamilyExists}\left(identityTransition\right) \land \neg \operatorname{GlobalSource}\left(constantFalseReadout, allTrueFamily\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation.compatible_family_exists_does_not_imply_global_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identity transitions make the all-true Fin 2 Boolean family compatible, while the constant-false readout from the nonempty global carrier Bool cannot realize that family.

**Theorem 1.5 (Readout compatibility is necessary for the first implication).**

$$\operatorname{GlobalSource}\left(constantFalseReadout, allFalseFamily\right) \land \neg \operatorname{ReadoutsCompatible}\left(twistedTransition, constantFalseReadout\right) \land \neg \operatorname{CompatibleFamilyExists}\left(twistedTransition\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation.readouts_compatible_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant-false family has a global source for the twisted finite system, but those readouts violate its reverse transition and no compatible family exists. Thus the omitted premise cannot be removed from level three implying level two.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation.compatible_family_exists_does_not_imply_global_source`
- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation.compatible_family_exists_implies_local_witnesses`
- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation.global_source_implies_compatible_family_exists`
- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation.local_witnesses_do_not_imply_compatible_family_exists`
- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation.readouts_compatible_is_necessary`
