# Coordinate Streamline Decomposition

## Abstract

Every unit-interval solenoid path has one compatible coordinate offset family.

**Theorem 1.1 (Every coordinate shares one compatible offset family).**

$$\begin{aligned}\forall \gamma: \operatorname{ContinuousMaps}\left([0, 1], UniversalSolenoid\right), \exists x: \operatorname{ContinuousMaps}\left([0, 1], \mathbb{R}\right),\\\exists c: CongruenceData, \forall m: PositiveNaturals, t: [0, 1],\\\operatorname{coord}\left(\gamma(t), m\right) = \operatorname{circleClass}\left(x(t) / m\right) + \operatorname{coord}\left(\operatorname{congruenceEmbedding}\left(c\right), m\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/Connectivity/CoordinateStreamlineDecomposition.exists_coordinate_streamline_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen interval decomposition supplies a continuous real lift and one constant element of the visible projection kernel.

The canonical exact-sequence theorem identifies that kernel element with a compatible residue at every positive modulus. Projecting the solenoid reconstruction at an arbitrary modulus gives the displayed circle-coordinate equation for every time.

The compatible residue family is quantified directly through the existing CongruenceData carrier; no duplicate coordinate or kernel primitive is introduced.

## References

- Truth anchor: `D5/S1/Solenoid/Connectivity/CoordinateStreamlineDecomposition.exists_coordinate_streamline_decomposition`
- Dependency: [D5/S1/Solenoid/ExactSequence](../ExactSequence.md)
- Dependency: [D5/S1/Solenoid/IntervalStreamlineDecomposition](../IntervalStreamlineDecomposition.md)
