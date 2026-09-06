# Qubit Empirical-Image Reflexive Gap

## Abstract

The exact qubit density-state readout is predicate-complete on its image but reflexively incomplete.

**Theorem 1.1 (Qubit empirical completeness does not imply reflexive completeness).**

$$\exists C: \operatorname{Fin}\left(3\right) \to \operatorname{RankOneContext}\left(2\right),\\{}\operatorname{let}\left(R, :, \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right) \to \left(\operatorname{Fin}\left(3\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right), \operatorname{fun}\left(rho, \operatorname{contextReadout}\left(C, \operatorname{ofMatrixInv}\left(\operatorname{value}\left(rho\right)\right)\right)\right)\right),\\{}\operatorname{Injective}\left(R\right) \land\\{}\operatorname{Bijective}\left(\operatorname{observablePullback}\left(R\right)\right) \land\\{}\forall catalog: \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right) \to \left(\operatorname{range}\left(R\right) \to Bool\right), \neg \operatorname{Surjective}\left(catalog\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Existence/QubitEmpiricalImageReflexiveGap.qubit_empirical_image_reflexive_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the displayed statement, ofMatrixInv denotes the Lean conversion CStarMatrix.ofMatrix.symm, which reads a density state's underlying matrix as a C*-matrix; R is the context readout. There is a three-context rank-one qubit observer whose readout R is injective on the full density-state subtype.

For that same R, pullback from Boolean predicates on its realized range is bijective, while every density-state-indexed catalog into that predicate space is non-surjective.

This specializes the abstract strict-gap theorem to the existing public qubit witness. It does not include concrete context-subfamily minimality because the source Pauli context is private.

## References

- Truth anchor: `D5/S3/Observer/Existence/QubitEmpiricalImageReflexiveGap.qubit_empirical_image_reflexive_gap`
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap](../../ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap.md)
- Dependency: [D5/S3/Observer/Existence/EmpiricalReflexiveSeparation](EmpiricalReflexiveSeparation.md)
