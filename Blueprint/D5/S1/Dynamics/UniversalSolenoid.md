# Universal One-Dimensional Solenoid

## Abstract

The universal one-dimensional solenoid carries its visible projection and dense real flow.

The carrier is the compatible family of circle phases indexed by positive integers under divisibility. Coordinate one defines a continuous, surjective additive projection to the visible circle.

A real parameter maps to the family represented in coordinate m by t/m. This is a continuous additive flow, its visible projection is t modulo one, and its image is dense. The density proof exactly matches every finite coordinate window by passing through a common multiple.

<a id="describe-universal-solenoid-projection-flow"></a>

**Theorem 1.1 (The real flow projects visibly and has dense range).**

$$\pi(\operatorname{realFlow}(t))=t\operatorname{mod}1.$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/UniversalSolenoid.projection_realFlow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projection formula is machine-checked directly. The same module proves dense range and derives connectedness from it.

## References

- Truth anchor: `D5/S1/Dynamics/UniversalSolenoid.projection_realFlow`
