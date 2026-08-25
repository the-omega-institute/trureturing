# Orbit Orientation

## Abstract

Readouts hide or expose free involutions; Boolean orientations are transversals.

**Theorem 1.1 (A Boolean orbit pair has exactly one local mode).**

$$\begin{gathered}\forall negation: \operatorname{InvolutiveNegation}\left(X\right),\\{}readout: X \to Bool, x: X,\\{}(\operatorname{readout}\left(readout, \operatorname{neg}\left(negation, x\right)\right) = \operatorname{readout}\left(readout, x\right) \lor \operatorname{readout}\left(readout, \operatorname{neg}\left(negation, x\right)\right) = \operatorname{not}\left(\operatorname{readout}\left(readout, x\right)\right)) \land\\{}\neg (\operatorname{readout}\left(readout, \operatorname{neg}\left(negation, x\right)\right) = \operatorname{readout}\left(readout, x\right) \land \operatorname{readout}\left(readout, \operatorname{neg}\left(negation, x\right)\right) = \operatorname{not}\left(\operatorname{readout}\left(readout, x\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/OrbitOrientation.boolean_orbit_exactly_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a chosen orbit point, a Boolean readout either agrees with its value on the paired point or equals the Boolean negation of that value.

The two alternatives cannot hold together, because no Boolean value equals its own negation. This is a local dichotomy and does not claim that one mode is chosen uniformly on all orbits.

**Theorem 1.2 (Negating readouts are exactly transversal supports).**

$$\forall negation: \operatorname{InvolutiveNegation}\left(X\right), readout: X \to Bool,\\{}\operatorname{NegatingReadout}\left(negation, readout\right) \iff \operatorname{OrbitTransversal}\left(negation, \operatorname{trueSupport}\left(readout\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/OrbitOrientation.negatingReadout_iff_trueSupport_transversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A globally negating Boolean readout changes truth value at every paired point. Its true support therefore contains exactly one side of each involutive orbit.

Conversely, if the true support is an orbit transversal, membership and nonmembership alternate across every pair. Exhausting the four Boolean value combinations yields the negating equation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Negation/OrbitOrientation.boolean_orbit_exactly_one`
- Truth anchor: `D5/S3/ConceptDynamics/Negation/OrbitOrientation.negatingReadout_iff_trueSupport_transversal`
- Dependency: [D5/S3/ConceptDynamics/Negation/InvolutiveNegation](InvolutiveNegation.md)
