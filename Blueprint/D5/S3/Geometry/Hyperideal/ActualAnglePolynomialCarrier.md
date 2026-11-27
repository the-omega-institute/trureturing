# Clipped original angles without winding aliases

## Abstract

An exact polynomial stationary certificate on the physical edge quotient of a hyperideal face pairing.

Each marked tetrahedron edge consumes the original six-cosh numerator and two positive face radicands. The first-quadrant unit half phase has squared-coordinate difference equal to the clipped cosine. Positive square roots and both saturated endpoints are expressed by polynomial conditions.

At a multiplication node, require nonnegative imaginary part and forbid both children to be minus one. The sum at each valid subtree then lies between zero and two pi in original-angle units. This is complete for an arbitrary binary bracketing; the endpoint alone is not complete.

**Theorem 1.1 (Exact winding certificate).**

$$\forall t \in \operatorname{PhaseCircuit}\left(\right),\; \left(\operatorname{Valid}\left(t\right) \land \operatorname{Phase}\left(t\right) = \operatorname{MinusOne}\left(\right)\right) \Leftrightarrow \left(\operatorname{LeavesInClosedInterval}\left(t\right) \land \operatorname{Angle}\left(t\right) = \operatorname{TwoPi}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/ActualAnglePolynomialCarrier.stationary_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A valid tree ending at minus one has exactly the target angle, even if leaves are zero or pi. Conversely every such total admits all binary bracketings.

**Theorem 1.2 (Actual carrier stationarity).**

$$\forall q \in \operatorname{ActualFacePairings}\left(\right),\; \forall x \in \operatorname{PositiveCoshData}\left(q\right),\; \operatorname{ExistsExactPolynomialFans}\left(q, x\right) \Leftrightarrow \operatorname{AllOriginalEdgeSumsAreTwoPi}\left(q, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/ActualAnglePolynomialCarrier.actual_pairing_algebraic_stationary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The program checks every physical edge of the face-pairing quotient and every one of its actual incidences. Repeated occurrences at the same physical edge are counted separately. Positive cosh inputs are required. This is a stationarity equivalence, not an assertion of geometric realization for every carrier.

Feng and Lin, Non-geometric ideal triangulations with all edge valences at least six, arXiv:2610.25217v2, sections 5.1, 6.4.3 and 6.4.4, use full phases and a winding certificate for their particular fans. The present half-phase tree test is exact per candidate at every finite valence. Quantifier elimination and the separate finite four-tetrahedron census are not asserted as Lean theorems here.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/ActualAnglePolynomialCarrier.actual_pairing_algebraic_stationary`
- Truth anchor: `D5/S3/Geometry/Hyperideal/ActualAnglePolynomialCarrier.stationary_iff`
- Dependency: [D5/S3/Geometry/Hyperideal/ActualCornerTransport](ActualCornerTransport.md)
- Dependency: [D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface](OriginalCosineDeterminantInterface.md)
