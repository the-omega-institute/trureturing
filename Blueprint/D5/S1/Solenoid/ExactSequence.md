# The Solenoid Exact Sequence

## Abstract

Compatible congruence data form exactly the kernel of the solenoid phase projection.

**Theorem 1.1 (Congruence data are exactly the invisible fiber).**

$$0 \to CongruenceData \to UniversalSolenoid \to UnitAddCircle \to 0, \operatorname{exact}$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/ExactSequence.congruence_solenoid_short_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A compatible residue at each positive modulus enters the corresponding circle coordinate through the canonical finite-torsion embedding. Compatibility makes these coordinates a solenoid element whose visible phase is zero. Conversely, every element with zero visible phase is torsion in each coordinate; choosing its unique finite residue and using coordinate compatibility reconstructs the congruence family. The inclusion is injective, its range is exactly the projection kernel, and the visible projection is surjective.

The pinned library was searched before construction. It supplies Function.Exact, ZMod.toAddCircle, ZMod.toAddCircle_injective, and AddCircle.nsmul_eq_zero_iff, but contains no solenoid definition or profinite-kernel exact sequence. This result is a new assembly from those library primitives rather than a thin wrapper. The source atom explicitly leaves its topological duality layer open; this theorem claims only the element-level exact sequence.

## References

- Truth anchor: `D5/S1/Solenoid/ExactSequence.congruence_solenoid_short_exact`
- Dependency: [D5/S1/Dynamics/UniversalSolenoid](../Dynamics/UniversalSolenoid.md)
