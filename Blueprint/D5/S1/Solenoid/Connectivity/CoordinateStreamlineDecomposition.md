# Coordinate Streamline Decomposition

## Abstract

Every compact real-interval solenoid path has one compatible coordinate offset family.

**Theorem 1.1 (Every coordinate shares one compatible offset family).**

$$\begin{aligned}\forall a, b: \mathbb{R}, \gamma: \operatorname{ContinuousMaps}\left([a, b], UniversalSolenoid\right),\\a \le b \Rightarrow \exists x: \operatorname{ContinuousMaps}\left([a, b], \mathbb{R}\right),\\\exists c: CongruenceData, \forall m: PositiveNaturals, t: [a, b],\\\operatorname{coord}\left(\gamma(t), m\right) = \operatorname{circleClass}\left(x(t) / m\right) + \operatorname{coord}\left(\operatorname{congruenceEmbedding}\left(c\right), m\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/Connectivity/CoordinateStreamlineDecomposition.exists_coordinate_streamline_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nondegenerate interval, the canonical affine homeomorphism transports the path to the unit interval. The frozen interval decomposition then supplies a continuous real lift and one constant element of the visible projection kernel. A singleton interval is transported by the constant unit-interval path, so ordered endpoints cover every nonempty compact real interval.

The canonical exact-sequence theorem identifies that kernel element with a compatible residue at every positive modulus. Projecting the solenoid reconstruction at an arbitrary modulus gives the displayed circle-coordinate equation for every time.

The compatible residue family is quantified directly through the existing CongruenceData carrier; no duplicate coordinate or kernel primitive is introduced.

## References

- Truth anchor: `D5/S1/Solenoid/Connectivity/CoordinateStreamlineDecomposition.exists_coordinate_streamline_decomposition`
- Dependency: [D5/S1/Solenoid/ExactSequence](../ExactSequence.md)
- Dependency: [D5/S1/Solenoid/IntervalStreamlineDecomposition](../IntervalStreamlineDecomposition.md)
