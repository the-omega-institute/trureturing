# Universal Solenoid Coordinate Scaling

## Abstract

A coordinate scaled by its index recovers the visible solenoid projection.

**Theorem 1.1 (Scaling any coordinate by its index gives the projection).**

$$\begin{aligned}\forall theta: UniversalSolenoid,\\\forall m: \mathbb{N}_{>0},\\m \cdot theta_{m} = \operatorname{projection}\left(theta\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/UniversalSolenoidCoordinate.nsmul_coordinate_eq_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A point theta of the universal solenoid is a family of circle coordinates, one for each positive integer index, compatible under divisibility. Reading that compatibility at index 1 says exactly that multiplying the index-m coordinate by m lands on the visible projection. This holds for every theta and every positive m, with no hypothesis on theta or its projection.

The value is an API one, not mathematical novelty. The proof is the defining compatibility field instantiated at index 1; nothing is discovered.

Three modules elsewhere in the repository each carry a private declaration of the projection theta = 0 special case; one of them packages theta as a point of the projection kernel. Those three modules are frozen and therefore cannot import this module. Naming the fact here removes none of those declarations, and this module has no Lean consumer today. What it adds is a public name for a statement that would otherwise be derived privately a fourth time.

All three private copies assume that the projection vanishes, while this identity needs no such hypothesis. The unconditional form is the primary theorem here, and those copies are its instances.

**Theorem 1.2 (A zero projection makes each coordinate index-torsion).**

$$\begin{aligned}\forall theta: UniversalSolenoid,\\\operatorname{projection}\left(theta\right) = 0 \Rightarrow\\\forall m: \mathbb{N}_{>0},\\m \cdot theta_{m} = 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/UniversalSolenoidCoordinate.nsmul_coordinate_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every solenoid point theta whose visible projection is zero, and for every positive integer m, multiplying the index-m circle coordinate by m gives zero. This is the special case that the three private declarations state.

The proof applies the unconditional coordinate-projection identity and then rewrites with the supplied vanishing hypothesis. It adds a public API name for the specialization, not a new mathematical argument.

## References

- Truth anchor: `D5/S1/Dynamics/UniversalSolenoidCoordinate.nsmul_coordinate_eq_projection`
- Truth anchor: `D5/S1/Dynamics/UniversalSolenoidCoordinate.nsmul_coordinate_eq_zero`
- Dependency: [D5/S1/Dynamics/UniversalSolenoid](UniversalSolenoid.md)
