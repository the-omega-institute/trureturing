# Clopen cylinders under the symbolic shift

## Abstract

Clopen symbolic cylinders and their exact shift pullback.

For a finite discrete directed graph, History G is the compact legal bi-infinite edge space. A cylinder fixes finitely many coordinates. The formal results below make the symbolic-to-topological bridge explicit: cylinders are clopen, and the left shift transports a cylinder by the corresponding inverse translate of its center.

**Theorem 1.1 (Finite cylinders are closed).**

$$cylinderClosed$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SymbolicCylinderShift.cylinder_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof identifies the cylinder with the inverse image of a finite product of singleton coordinate sets and uses the product topology and the subspace topology on legal histories.

**Theorem 1.2 (Finite cylinders are clopen).**

$$cylinderIsClopen$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SymbolicCylinderShift.cylinder_isClopen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining the existing finite-coordinate openness theorem with the closedness result gives the clopen basis used by symbolic dynamics.

**Theorem 1.3 (Cylinders form a local topological basis).**

$$existsCylinderSubset$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SymbolicCylinderShift.exists_cylinder_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every open neighborhood of a legal history contains a finite-coordinate cylinder around that history. This is the local basis statement that turns finite symbolic observations into genuine topological neighborhoods.

**Theorem 1.4 (The shift has an exact cylinder pullback).**

$$shiftPreimageCylinder$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SymbolicCylinderShift.shift_preimage_cylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite coordinate set s and center x, the preimage under the left shift is the cylinder on s shifted by k↦k+1, centered at translate(-1,x). This equality is pointwise and does not use a metric, measure, entropy limit, or a hidden coding assumption.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/SymbolicCylinderShift.cylinder_closed`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SymbolicCylinderShift.cylinder_isClopen`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SymbolicCylinderShift.exists_cylinder_subset`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SymbolicCylinderShift.shift_preimage_cylinder`
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms](StandardBeamHomeomorphisms.md)
